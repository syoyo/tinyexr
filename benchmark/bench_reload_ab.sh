#!/bin/sh
# A/B repeated whole-image load benchmark: current tree vs a baseline revision.
#
# Builds the baseline library in a detached git worktree, builds the same
# benchmark source against both libraries with identical flags, then alternates
# fresh-process runs and reports medians. Nothing is committed and the worktree
# is removed on exit.
#
# usage: bench_reload_ab.sh FIXTURE [LOADS] [REPS] [BASE_REF]
#   FIXTURE   path to an .exr file (e.g. the 660x440 photographic PIZ fixture)
#   LOADS     loads per process (default 300)
#   REPS      fresh processes per side (default 9)
#   BASE_REF  git revision to compare against (default ef203db)
set -eu

here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)

fixture=${1:-}
loads=${2:-300}
reps=${3:-9}
base_ref=${4:-ef203db}

if [ -z "$fixture" ]; then
    echo "usage: $0 FIXTURE [LOADS] [REPS] [BASE_REF]" >&2
    exit 2
fi
[ -f "$fixture" ] || { echo "missing fixture: $fixture" >&2; exit 2; }
case $fixture in
    /*) ;;
    *) fixture=$(pwd)/$fixture ;;
esac
[ "$reps" -ge 1 ] 2>/dev/null || { echo "REPS must be >= 1" >&2; exit 2; }

: "${CC:=cc}"
: "${JOBS:=$(nproc 2>/dev/null || echo 4)}"

tmp=$(mktemp -d "${TMPDIR:-/tmp}/exr-reload-ab.XXXXXX")
cleanup() {
    git -C "$root" worktree remove --force "$tmp/base" >/dev/null 2>&1 || true
    if [ "${KEEP:-0}" = 1 ]; then
        echo "kept raw results in $tmp" >&2
    else
        rm -rf "$tmp"
    fi
}
trap cleanup EXIT INT TERM

echo "baseline=$base_ref loads=$loads reps=$reps fixture=$fixture" >&2

git -C "$root" worktree add --detach "$tmp/base" "$base_ref" >/dev/null
( cd "$tmp/base" && make -B -j "$JOBS" lib THREADS=1 >/dev/null )
"$CC" -std=c11 -O2 -I"$tmp/base/include" "$here/bench_reload.c" \
    "$tmp/base/build/libtinyexr3.a" -lm -o "$tmp/bench_base"

( cd "$root" && make -B -j "$JOBS" lib THREADS=1 >/dev/null )
"$CC" -std=c11 -O2 -I"$root/include" "$here/bench_reload.c" \
    "$root/build/libtinyexr3.a" -lm -o "$tmp/bench_cur"

: > "$tmp/results"
i=1
while [ "$i" -le "$reps" ]; do
    for side in base cur; do
        "$tmp/bench_$side" "$fixture" "$loads" 6 1 | tail -n +2 |
        while IFS=, read -r fbytes mode thr ms flt peak; do
            printf '%s,%s,%s,%s,%s,%s\n' \
                "$side" "$i" "$mode" "$ms" "$flt" "$peak" >> "$tmp/results"
        done
    done
    i=$((i + 1))
done

median() { sort -n | awk '{ a[NR] = $1 } END { if (NR) print a[int((NR + 1) / 2)] }'; }

printf '%-10s %-9s %12s %13s %14s %9s\n' \
    variant mode ms_per_load minflt_per_load peak_bytes delta
for mode in file file+ctx; do
    for side in base cur; do
        awk -F, -v s="$side" -v m="$mode" '$1 == s && $3 == m { print $4 }' \
            "$tmp/results" > "$tmp/ms_${side}_${mode}"
        awk -F, -v s="$side" -v m="$mode" '$1 == s && $3 == m { print $5 }' \
            "$tmp/results" > "$tmp/flt_${side}_${mode}"
        awk -F, -v s="$side" -v m="$mode" '$1 == s && $3 == m { print $6 }' \
            "$tmp/results" > "$tmp/peak_${side}_${mode}"
    done
    base_ms=$(median < "$tmp/ms_base_${mode}")
    cur_ms=$(median < "$tmp/ms_cur_${mode}")
    if [ -z "$base_ms" ] || [ -z "$cur_ms" ]; then
        echo "$mode: SKIPPED (missing measurements; see stderr)" >&2
        continue
    fi
    cur_flt=$(median < "$tmp/flt_cur_${mode}")
    base_flt=$(median < "$tmp/flt_base_${mode}")
    cur_peak=$(awk '{ if ($1 > m) m = $1 } END { print m + 0 }' \
        "$tmp/peak_cur_${mode}")
    delta=$(awk -v b="$base_ms" -v c="$cur_ms" \
        'BEGIN { printf "%+.1f%%", (c - b) * 100 / b }')
    printf '%-10s %-9s %12.3f %13.1f %14s %9s\n' \
        "$base_ref" "$mode" "$base_ms" "$base_flt" - "$delta"
    printf '%-10s %-9s %12.3f %13.1f %14s %9s\n' \
        "current" "$mode" "$cur_ms" "$cur_flt" "$cur_peak" "vs base"
done

echo "raw results: set KEEP=1 to retain the temporary directory" >&2
