# Lean formalization plan and current status

- **Repository:** `/mnt/disk01/work/tinyexr`
- **Branch:** `release`
- **Branch:** `release`
- **Status source of truth:** `git log --oneline` and `make lean-status`.
  Static counts are intentionally not duplicated here because they change with
  every proof slice.

## Rules

- Never push without explicit permission. Before pushing, run both `gitleaks`
  and `trufflehog` over `origin/release..HEAD`.
- Do not implement DWAA/DWAB. Do not refactor HTJ2K/JPH internals without the
  owner's coordination. Do not modify legacy `tinyexr.h`.
- C remains pure C11; hostile-input arithmetic uses `exr_mul_ovf`/`exr_add_ovf`;
  SIMD must be bit-identical to scalar and scalar is the source of truth.
- Lean additions must be `sorry`-free, carry the BSD-3-Clause header, and pass
  `make lean-axiom-check`.
- Every executable Lean change needs a C-vs-Lean differential gate with zero
  mismatches and a negative control where practical.
- Keep `lean/README.md` and `lean/VERIFICATION.md` synchronized with the model.

## Completed coverage

- **EXR core:** parser/emitter structure, PXR24, B44/B44A, RLE, ZIP/PIZ, deep
  payload algebra, generated-file validation, reader error/ownership state,
  shared header validation, image-budget and tile-geometry guards.
- **DEFLATE:** stored, fixed and dynamic-Huffman decoding with LZ77 overlap
  copies and zlib framing/Adler validation (`deflate-diff`).
- **HTJ2K/JPH wrapper:** marker sequence, SIZ geometry, profile checks and tile
  counts (`jph-diff`); entropy internals remain separately owned.
- **Tir:** geometry, edge mapping, window tables/measure-fill agreement,
  scalar kernels/converters and streaming state (`tir-diff`,
  `tir-kernel-diff`, `tir-streaming-diff`).
- **Texcomp:** block models plus public image encode/decode drivers for
  BC1/3/4/5/6H/7, ETC2/EAC, ASTC LDR/HDR/UASTC and uni transcodes. Image paths
  are byte-exact against C. Structural proofs cover BC6H/BC7 wire writers and
  byte layouts, BC6H signed fields and candidate monotonicity, BC7 weight
  symmetry, ASTC HDR void extents and float-output image lengths.
- **Tocio:** parser/config/processor lowering, loaders, builtins, scalar/JIT/SIMD
  parity, AOT-C/GLSL/Metal emitters and emitted-statement semantics for the
  modelled op set. The total YAML parser's depth, height and remaining-fuel
  bounds are proved.
- **Shared math:** libm-free fast/accurate/exact scalar math, differential gates
  and ULP sweeps.

## Remaining proof-level work

### Priority 1 — status and documentation hygiene

1. `make lean-status` and `make lean-diff-all` are implemented.
2. `plan.md`, `resume-lean.md`, the README conformance matrix and documented
   boundaries are synchronized with the current model.
3. The full differential matrix is green: all 80 discovered `*-diff` targets
   passed with zero mismatches; `make lean-status` and the C gates were re-run
   for the close-out.

### Priority 2 — proof hardening

Completed initial slices:

1. **Texcomp wire/output contracts:** BC6H writer, tail budget, byte layout,
   signed fields and candidate monotonicity; BC7 writer/packing/weight symmetry;
   ASTC HDR void extents; float-output image lengths.
2. **Tocio YAML fuel semantics:** `parseTotal_used_le` proves the returned value
   is remaining fuel bounded by the input fuel. A literal total-calls ≤
   branch-local-fuel theorem is not the current semantics; the C-faithful
   engine deliberately keeps an input-size work-fuel over-approximation.
3. **Tocio codegen semantics:** the audit found no additional emitted op path
   outside the proved matrix/range/LUT/exponent/log/CDL/fixed-function set;
   byte-identical text gates remain the C link.
4. **Accurate math ULP boundary:** `Math/F32ULP.lean` proves metric laws,
   exactness on all 254 normal powers and tight worst-bit witnesses; exhaustive
   C sweeps cover every normal `log2f`, every in-range `exp2f`/`expf`, and every
   positive-normal `powf(x,1)` input (maxima 3/1/1/44 ULP). A universal analytic
   arbitrary-mantissa ULP theorem remains the open proof boundary.

Optional deeper follow-ups: endpoint-swap reconstruction invariance, LSQ and
quantizer range algebra, a cost-returning YAML engine variant, and a universal
analytic ULP proof for the accurate math tier.

### Accepted boundaries

- DWAA/DWAB remain unsupported.
- JPH entropy decoding is separately owned.
- DEFLATE encoder-side LZ77 match selection is not modelled.
- B44 perceptual table interior derivation is not modelled.
- Universal analytic arbitrary-mantissa ULP bounds for the accurate math tier
  are not formally proved. The entire positive-normal `powf(x,1)` domain, all
  normal `log2f` inputs and all in-range `exp2f` inputs are exhaustively swept
  by the C gate; formal dyadic exactness and tight worst-bit witnesses are
  proved.
- The C-faithful YAML engine has no exact total-call metric; its work fuel is
  an input-size over-approximation. The total parser's remaining-fuel bound is
  proved.
- The Lean model is not a proof of C execution semantics; differential and
  sanitizer gates provide the implementation link.
