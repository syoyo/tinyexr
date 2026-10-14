/*
 * TinyEXR - optional C11-threads worker pool for per-block parallel codec work.
 *
 * Gated by EXR_USE_THREADS (default off). When enabled, exr_parallel_for spawns
 * an ephemeral set of workers that pull jobs from a shared, mutex-protected
 * counter; the calling thread participates too. The workers come from C11
 * <threads.h> where available, or Grand Central Dispatch on macOS/Apple
 * platforms (which do not ship <threads.h>). When disabled (the default, and
 * always for freestanding builds) it runs the jobs serially and pulls in no
 * threading headers.
 *
 * The thread-count setter/getter are always defined so the public API exists in
 * every build; they simply have no effect when threads are compiled out.
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "exr_internal.h"

/* Process-global worker count (always present; >1 only matters with threads). */
static int g_num_threads = 1;

void exr_set_num_threads(int n) { g_num_threads = (n < 1) ? 1 : n; }
int exr_get_num_threads(void) { return g_num_threads; }

#if defined(EXR_USE_THREADS) && defined(__APPLE__)

/* Apple platforms do not ship C11 <threads.h>; use Grand Central Dispatch and
 * os_unfair_lock, both native (in libSystem, no extra link flags). We spawn
 * nthreads-1 GCD workers via dispatch_group_async_f (a C function pointer, so
 * no Objective-C blocks / -fblocks needed); the calling thread is the nth
 * worker. All of them drain the same shared, lock-guarded job counter, exactly
 * like the C11 path below. */
#include <dispatch/dispatch.h>
#include <os/lock.h>

typedef struct {
    exr_par_fn fn;
    void *ctx;
    int njobs;
    int next; /* next unclaimed job index, guarded by lock */
    os_unfair_lock lock;
} par_state;

static void par_worker(void *arg) {
    par_state *st = (par_state *)arg;
    for (;;) {
        int job;
        os_unfair_lock_lock(&st->lock);
        job = (st->next < st->njobs) ? st->next++ : -1;
        os_unfair_lock_unlock(&st->lock);
        if (job < 0) break;
        st->fn(st->ctx, job);
    }
}

void exr_parallel_for(int nthreads, int njobs, exr_par_fn fn, void *ctx) {
    par_state st;
    dispatch_queue_t q;
    dispatch_group_t grp;
    int i;

    if (njobs <= 0) return;
    if (nthreads > njobs) nthreads = njobs;
    if (nthreads <= 1) { /* serial */
        for (i = 0; i < njobs; ++i) fn(ctx, i);
        return;
    }

    st.fn = fn;
    st.ctx = ctx;
    st.njobs = njobs;
    st.next = 0;
    st.lock = (os_unfair_lock)OS_UNFAIR_LOCK_INIT;

    /* st lives on this stack frame; dispatch_group_wait below keeps it alive
     * for the whole worker lifetime, so capturing &st is safe. */
    q = dispatch_get_global_queue(QOS_CLASS_USER_INITIATED, 0);
    grp = dispatch_group_create();
    if (!grp || !q) {
        if (grp) dispatch_release(grp);
        for (i = 0; i < njobs; ++i) fn(ctx, i);
        return;
    }
    for (i = 0; i < nthreads - 1; ++i)
        dispatch_group_async_f(grp, q, &st, par_worker);

    par_worker(&st); /* calling thread participates */

    dispatch_group_wait(grp, DISPATCH_TIME_FOREVER);
    dispatch_release(grp);
}

#elif defined(EXR_USE_THREADS)

#if defined(EXR_THREADS_PTHREAD)
#include <pthread.h>
typedef pthread_t exr_thread_t;
typedef pthread_mutex_t exr_mutex_t;
typedef void *exr_thread_ret;
#define EXR_THREAD_RET_OK NULL
static int exr_mutex_init(exr_mutex_t *m) { return pthread_mutex_init(m, NULL) == 0; }
static void exr_mutex_lock(exr_mutex_t *m) { (void)pthread_mutex_lock(m); }
static void exr_mutex_unlock(exr_mutex_t *m) { (void)pthread_mutex_unlock(m); }
static void exr_mutex_destroy(exr_mutex_t *m) { (void)pthread_mutex_destroy(m); }
static int exr_thread_create(exr_thread_t *t, exr_thread_ret (*fn)(void *),
                             void *arg) {
    return pthread_create(t, NULL, fn, arg) == 0;
}
static void exr_thread_join(exr_thread_t t) { (void)pthread_join(t, NULL); }
#else
#include <threads.h>
typedef thrd_t exr_thread_t;
typedef mtx_t exr_mutex_t;
typedef int exr_thread_ret;
#define EXR_THREAD_RET_OK 0
static int exr_mutex_init(exr_mutex_t *m) { return mtx_init(m, mtx_plain) == thrd_success; }
static void exr_mutex_lock(exr_mutex_t *m) { (void)mtx_lock(m); }
static void exr_mutex_unlock(exr_mutex_t *m) { (void)mtx_unlock(m); }
static void exr_mutex_destroy(exr_mutex_t *m) { mtx_destroy(m); }
static int exr_thread_create(exr_thread_t *t, exr_thread_ret (*fn)(void *),
                             void *arg) {
    return thrd_create(t, fn, arg) == thrd_success;
}
static void exr_thread_join(exr_thread_t t) { (void)thrd_join(t, NULL); }
#endif

/* Upper bound on workers, so the thread handle array can live on the stack and
 * a pathological count cannot exhaust resources. */
#define EXR_THREAD_CAP 64

typedef struct {
    exr_par_fn fn;
    void *ctx;
    int njobs;
    int next; /* next unclaimed job index, guarded by lock */
    exr_mutex_t lock;
} par_state;

static exr_thread_ret par_worker(void *arg) {
    par_state *st = (par_state *)arg;
    for (;;) {
        int job;
        exr_mutex_lock(&st->lock);
        job = (st->next < st->njobs) ? st->next++ : -1;
        exr_mutex_unlock(&st->lock);
        if (job < 0) break;
        st->fn(st->ctx, job);
    }
    return EXR_THREAD_RET_OK;
}

void exr_parallel_for(int nthreads, int njobs, exr_par_fn fn, void *ctx) {
    par_state st;
    exr_thread_t threads[EXR_THREAD_CAP];
    int spawned = 0, i;

    if (njobs <= 0) return;
    if (nthreads > njobs) nthreads = njobs;
    if (nthreads > EXR_THREAD_CAP) nthreads = EXR_THREAD_CAP;
    if (nthreads <= 1) { /* serial */
        for (i = 0; i < njobs; ++i) fn(ctx, i);
        return;
    }

    st.fn = fn;
    st.ctx = ctx;
    st.njobs = njobs;
    st.next = 0;
    if (!exr_mutex_init(&st.lock)) {
        for (i = 0; i < njobs; ++i) fn(ctx, i); /* fallback: serial */
        return;
    }

    /* Spawn up to nthreads-1 helpers; the calling thread is the nth worker.
     * If a spawn fails we simply have fewer workers - correctness is unaffected
     * because every worker drains the same shared job counter. */
    for (i = 0; i < nthreads - 1; ++i) {
        if (exr_thread_create(&threads[spawned], par_worker, &st))
            ++spawned;
    }

    par_worker(&st); /* calling thread participates */

    for (i = 0; i < spawned; ++i) exr_thread_join(threads[i]);
    exr_mutex_destroy(&st.lock);
}

#else /* !EXR_USE_THREADS : serial, no <threads.h> (freestanding-safe) */

void exr_parallel_for(int nthreads, int njobs, exr_par_fn fn, void *ctx) {
    int i;
    (void)nthreads;
    for (i = 0; i < njobs; ++i) fn(ctx, i);
}

#endif /* EXR_USE_THREADS */
