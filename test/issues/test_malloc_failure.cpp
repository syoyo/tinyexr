// Test malloc failure handling - verifies no crashes on allocation failure
// Build: g++ -std=c++17 test_malloc_failure.cpp -lz -o test && ./test
#include <cstdio>
#include <cstdlib>
#include <signal.h>
#include <setjmp.h>

static int g_fail_at = -1, g_count = 0;
static sigjmp_buf g_jmp;

// Signal handler - jump back to test loop on crash
static void on_crash(int sig) { siglongjmp(g_jmp, sig); }

// Fake allocators - return NULL at g_fail_at'th call
static void* fake_malloc(size_t sz) { return (++g_count == g_fail_at) ? NULL : malloc(sz); }
static void* fake_realloc(void* p, size_t sz) { return (++g_count == g_fail_at) ? NULL : realloc(p, sz); }
static void* fake_calloc(size_t n, size_t sz) { return (++g_count == g_fail_at) ? NULL : calloc(n, sz); }

// Intercept allocators before including tinyexr
#define malloc fake_malloc
#define realloc fake_realloc
#define calloc fake_calloc

#define TINYEXR_IMPLEMENTATION
#define TINYEXR_USE_MINIZ 0
#include <zlib.h>
#include "../../tinyexr.h"

int main() {
    float pixels[64] = {0};
    int crashes = 0;

    // Baseline run - count mallocs with no failures
    g_fail_at = -1;
    g_count = 0;
    unsigned char* out = NULL;
    const char* err = NULL;
    SaveEXRToMemory(pixels, 4, 4, 4, 0, &out, &err);
    if (out) free(out);
    if (err) FreeEXRErrorMessage(err);
    int num_mallocs = g_count;

    printf("Testing %d mallocs:\n", num_mallocs);

    // Test each malloc failure point
    for (int i = 1; i <= num_mallocs; i++) {
        g_fail_at = i;
        g_count = 0;
        out = NULL;
        err = NULL;

        signal(SIGSEGV, on_crash);           // Re-register handler each iteration
        if (sigsetjmp(g_jmp, 1) == 0) {      // Returns 0 on first call
            int ret = SaveEXRToMemory(pixels, 4, 4, 4, 0, &out, &err);
            printf("  #%d: ret=%d %s\n", i, ret, err ? err : "");
            if (out) free(out);
            if (err) FreeEXRErrorMessage(err);
        } else {                             // Returns sig after siglongjmp from crash
            printf("  #%d: CRASH\n", i);
            crashes++;
        }
    }

    printf(crashes ? "FAILED: %d crashes\n" : "PASSED\n", crashes);
    return crashes;
}
