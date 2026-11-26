# Resume prompt: TinyEXR v3 Lean formalization

Repository: `/mnt/disk01/work/tinyexr`, branch `release`. Read `AGENTS.md`,
`lean/README.md`, `lean/VERIFICATION.md` and `plan.md` first.

## Rules

- Never push without explicit permission. Before any push, run both secret
  scans over `origin/release..HEAD`:
  - `gitleaks detect --source . --log-opts="origin/release..HEAD" --no-banner --redact`
  - `~/go/bin/trufflehog git "file://$(pwd)" --since-commit <base-hash> --branch HEAD --results=verified,unknown --no-update --fail`
- Do not implement DWAA/DWAB. Do not refactor HTJ2K/JPH internals. Do not touch
  legacy `tinyexr.h`.
- C stays pure C11; hostile-input arithmetic uses `exr_mul_ovf`/`exr_add_ovf`.
  SIMD must be bit-identical to scalar.
- No Lean `sorry`/`admit`. `make lean-axiom-check` must stay green.
- A Lean change is not complete until its differential gate reports zero
  mismatches and the README/VERIFICATION docs are updated.

## Current state

- `release` is pushed through `5e27c7a` (all proof-hardening work to date);
  future status/proof work stays local until the user explicitly permits a push.
- Run `make lean-status` for current file/line/theorem counts and
  `make lean-axiom-check` for the transitive axiom census.
- Latest close-out: 330 Lean files, 57,456 lines and 1,596 source-level
  theorem/lemma declarations; axiom audit 4,968 first-party theorems;
  80/80 differential targets green.
- EXR core/codecs, DEFLATE decode, JPH wrapper, Tir, texcomp image drivers,
  Tocio engine/codegen and shared scalar math are all modelled and gated.
- BC6H/BC7 wire and output contracts, BC7 weight reversal/endpoint-swap
  interpolation, ASTC HDR void extents, the total YAML parser's remaining-fuel
  bound, and accurate-math dyadic/direct-identity theorems are proved. The accurate `log2f`/`exp2f`/`logf`/`powf` tier now uses
  binary64 intermediates with exhaustive practical-domain validation; see
  `math-accurate-ulp` and `math-pow-one-ulp`.

## Core gates

```sh
make lean-check
make lean-status
make lean-diff-all
make lean-axiom-check
make lean-validation-test
make lean-validation-sanitize
make test-c
make fuzz-corpus
make tools-test
```

`lean-diff-all` discovers every `*-diff` target in the Makefile and runs them
sequentially to avoid races in shared generated-vector directories.

## Suggested next steps

1. If there are uncommitted changes, run the relevant focused gates first.
2. Pick a Priority 2 proof slice from `plan.md`; keep model, theorem, gate and
   documentation in the same commit.
3. Run `make lean-diff-all` after broad proof changes.
4. Run both secret scans and ask for explicit push permission.
