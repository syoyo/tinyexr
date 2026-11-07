#!/usr/bin/env bash
# SPDX-License-Identifier: BSD-3-Clause
# Fetch, pin, patch and build the upstream Ptex reference used by the opt-in
# differential suite (`make ptex-compare`). Nothing here runs in the default
# build or in `make tools-test`.
#
# Steps: clone wdas/ptex (or reuse PTEX_UPSTREAM_SRC), verify HEAD is the pinned
# commit, apply the portability patch, build a static libPtex with
# -ffp-contract=off, then run upstream's own tests as a canary: if the oracle
# itself is miscompiled (e.g. the GCC 15.2 wrong-code bug that crashes
# constant-face allocation), the suite aborts instead of comparing against it.
#
# Environment:
#   PTEX_UPSTREAM_SRC   existing checkout to use instead of cloning
#   PTEX_UPSTREAM_DIR   work dir (default: <repo>/build/ptex-upstream)
#   PTEX_CXX            C++ compiler (default: clang++, g++-14, g++ in that order)
# Prints the include dir and library path on success:
#   PTEX_INCLUDE=...  PTEX_LIB=...
set -euo pipefail

PINNED_TAG="v2.4.3"
PINNED_COMMIT="4aa2c35f9f25f025014fbbbf41cef669881b4172"
URL="https://github.com/wdas/ptex.git"

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(cd "$here/../../.." && pwd)"
work="${PTEX_UPSTREAM_DIR:-$repo/build/ptex-upstream}"
src="${PTEX_UPSTREAM_SRC:-$work/src}"
bld="$work/build"
mkdir -p "$work"

if [[ ! -f "$src/src/ptex/Ptexture.h" ]]; then
  echo "[fetch] cloning $URL ($PINNED_TAG) into $src" >&2
  git clone --depth 1 --branch "$PINNED_TAG" "$URL" "$src" >&2
fi
head="$(git -C "$src" rev-parse HEAD)"
if [[ "$head" != "$PINNED_COMMIT" ]]; then
  echo "FAIL: upstream HEAD $head is not the pinned commit $PINNED_COMMIT" >&2
  exit 1
fi

# GCC 15.2 wrong-code workaround (AtomicLoad on PtexHashMap); idempotent.
if git -C "$src" apply --check "$here/openptex-portable-constant-face.patch" 2>/dev/null; then
  git -C "$src" apply "$here/openptex-portable-constant-face.patch"
  echo "[fetch] applied openptex-portable-constant-face.patch" >&2
elif git -C "$src" apply --check --reverse "$here/openptex-portable-constant-face.patch" 2>/dev/null; then
  echo "[fetch] portability patch already applied" >&2
else
  echo "FAIL: portability patch neither applies nor is already applied" >&2
  exit 1
fi

cxx="${PTEX_CXX:-}"
if [[ -z "$cxx" ]]; then
  for c in clang++ g++-14 g++; do
    if command -v "$c" >/dev/null 2>&1; then cxx="$c"; break; fi
  done
fi
[[ -n "$cxx" ]] || { echo "FAIL: no C++ compiler found" >&2; exit 1; }
if "$cxx" --version 2>/dev/null | grep -Eq '(g\+\+|GCC).* 15\.'; then
  echo "WARN: GCC 15 miscompiles unpatched OpenPtex; relying on the portability patch + canary" >&2
fi

echo "[fetch] building upstream with $cxx" >&2
cmake -S "$src" -B "$bld" -G "${PTEX_CMAKE_GENERATOR:-Unix Makefiles}" \
  -DCMAKE_BUILD_TYPE=Release -DCMAKE_CXX_COMPILER="$cxx" \
  -DCMAKE_CXX_FLAGS="-O1 -ffp-contract=off -fno-strict-aliasing" \
  -DPTEX_BUILD_STATIC_LIB=ON -DPTEX_BUILD_SHARED_LIBS=OFF >&2
cmake --build "$bld" -j"$(nproc 2>/dev/null || echo 4)" >&2

# Canary: upstream's own tests (wtest/rtest/ftest/halftest) must pass.
if ! (cd "$bld" && ctest --output-on-failure >&2); then
  echo "FAIL: upstream's own tests fail with this toolchain; the oracle is untrusted" >&2
  exit 1
fi

lib="$(find "$bld" -name 'libPtex*.a' | head -1)"
[[ -n "$lib" ]] || { echo "FAIL: libPtex static library not found" >&2; exit 1; }
# PtexVersion.h is generated into the build tree.
gen="$(dirname "$(find "$bld" -name PtexVersion.h | head -1)")"
echo "PTEX_INCLUDE=$src/src/ptex"
echo "PTEX_GEN_INCLUDE=$gen"
echo "PTEX_LIB=$lib"
echo "PTEX_CXX=$cxx"
