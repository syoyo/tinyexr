#!/usr/bin/env bash
# SPDX-License-Identifier: BSD-3-Clause
# Opt-in differential suite: build every cmp_*.cc against tptex and the pinned
# upstream OpenPtex, then run them. Reached through `make ptex-compare`.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(cd "$here/../../.." && pwd)"
out="$repo/build/ptex-compare"
mkdir -p "$out"

eval "$("$here/fetch_ptex.sh" | tee "$out/upstream.env")"
cxx="${PTEX_CXX:-g++}"
inc=(-I"$PTEX_INCLUDE" -I"$PTEX_GEN_INCLUDE" -I"$repo/tools/ptex/include")
# tptex is plain C11: compile it as C so the comparison exercises the C build.
cc="${CC:-cc}"
objs=("$out/miniz.o")
"$cc" -std=c11 -O2 -I"$repo/deps/miniz" -c "$repo/deps/miniz/miniz.c" -o "$out/miniz.o"
for f in "$repo"/tools/ptex/src/tptex_*.c; do
  case "$f" in *tptex_file.c) continue;; esac
  o="$out/$(basename "$f" .c).o"
  "$cc" -std=c11 -O1 -g ${TPTEX_SAN:+-fsanitize=address,undefined -fno-sanitize-recover=undefined} -ffp-contract=off -I"$repo/tools/ptex/include" -I"$repo/tools/ptex/src" -I"$repo/deps/miniz" -c "$f" -o "$o"
  objs+=("$o")
done

fail=0
for t in "$here"/cmp_*.cc; do
  name="$(basename "$t" .cc)"
  echo "== $name"
  "$cxx" -std=c++17 -O1 -g ${TPTEX_SAN:+-fsanitize=address,undefined -fno-sanitize-recover=undefined} -ffp-contract=off "${inc[@]}" "$t" "${objs[@]}" "$PTEX_LIB" -lz -lpthread -o "$out/$name"
  "$out/$name" "$out" || fail=1
done
exit $fail
