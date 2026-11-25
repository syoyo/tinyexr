# Resume prompt: TinyEXR v3 Lean formalization

Repo: `/mnt/disk01/work/tinyexr`, branch `release`. Read `AGENTS.md` and `lean/README.md` first.

## Rules that stay in force
- **Never push without explicit permission** ("push it"). Before any push, run **gitleaks and trufflehog**; both must exit 0.
  - gitleaks: `gitleaks detect --source . --log-opts="origin/release..HEAD" --no-banner --redact`
  - trufflehog: the plain AGENTS.md command scans 0 chunks here. Use `~/go/bin/trufflehog git "file://$(pwd)" --since-commit <base-hash> --branch HEAD --results=verified,unknown --no-update --fail`.
- Do **not** implement DWAA/DWAB. Do not refactor HTJ2K/JPH. Do not touch the legacy `tinyexr.h`.
- C library: hostile-input arithmetic goes through `exr_mul_ovf`/`exr_add_ovf`. SIMD must be bit-identical to scalar, and scalar is the source of truth.
- A Lean change is not done until its differential gate (a C vector generator versus a Lean checker exe) shows 0 mismatches.
- `make lean-axiom-check` must stay green. `native_decide` is allowed only for the ten approved generator checks. No `sorry`.
- Commit messages end with `Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>`.
- Temp files go in the session scratchpad, not `/tmp`.

## State
- Local HEAD is `e57fe2b` ("bring four more library modules into the axiom audit"). It is **not pushed**. `origin/release` is at `5dad810`, and CI was all green (16 jobs) on that commit.
- The Lean model covers:
  - EXR structure and codecs (PXR24, B44, RLE, ADLER32, Deep).
  - tocio.
  - texcomp: BC1/3/4/5/6H/7, ETC2/EAC encode and decode, ASTC LDR/HDR/UASTC, the uni container, and the uni transcodes to ASTC, BC1, BC7 and ETC2.
- `make lean-axiom-check` audits 3919 theorems with no unexpected axioms.
- Audit scope: `lean/ExrSpec.lean` is the module root the audit enumerates. A module only imported by its own `*Check` exe is **not** audited.
  - Deliberately excluded:
    - `Bc7Mode0` and `Etc2TModeDecode3`: superseded, and they redefine names.
    - `Tocio.FloatSemantics`: unapproved `native_decide`.
    - the `*Dbg` modules.

## Known unmodelled boundaries
- BC7 with `rdo > 0` (`tc_bc7_rdo_pass`). `Bc7Rdo.lean` exists, but uni never enables it.
- The ETC2 planar float code assumes no FMA contraction. GCC on AArch64 would need `-ffp-contract=off`.
- The DEFLATE bitstream, and DWAA/DWAB (out of scope by policy).

## Gates
`make lean-check`, `lean-diff`, `codec-diff`, `lean-axiom-check`, `lean-gen-check`, `texcomp-uni-diff`, `texcomp-uni-transcode-diff`, `texcomp-etc2-enc-diff`, `texcomp-astc-ldrdec-diff`.

`make lean-openexr-test` fails locally only because `libopenexr-dev` is missing. CI installs it, so ignore that failure here.

## Suggested next steps
1. Ask the user whether to push `e57fe2b`. Run both secret scans first, and check CI after the push.
2. Run the full `make lean-check` once, since only `lake build ExrSpec` and the axiom check were run for the last commit.
3. Pick any remaining item from the boundaries list above only if the user asks for it.
