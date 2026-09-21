# Independent review: actual finite Toeplitz inverse assembly

Verdict: **APPROVE** the statements and assembly proofs in
`ToeplitzInverse.lean` and the generic matrix algebra it uses. The actual
matrix is proved to have the displayed right inverse, Mathlib's genuine
matrix inverse is identified with it, and every finite entry is expanded
with the correct indices. This review expressly excludes independent
review of this reviewer's own weighted-factorization dependency.

Reviewer: `/root/mf21_restart_lean_audit`, 20 September 2026. Both reviewed
modules were authored by the coordinator, not this reviewer. No source
edits or compiler runs were performed during this review. The pinned
referee standards have SHA256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Exact files and local evidence

| Artifact | SHA256 |
|---|---|
| `MF21Restart/ToeplitzInverse.lean` | `cd5af3cf32a12d55ff2c7499b5d47e05b1d5192d3675b837ca053a647cf6d39e` |
| `TOEPLITZ_INVERSE_STATEMENTS.md` | `e126f4e65ba8e073403baa889b1008340aa9e2c6abfd7ace95d5c5dd1e559f2e` |
| `evidence/logs/toeplitz-inverse-01.json` | `9dbf0284518e08d243e25a5eed0a7b549ef7b90014edb7b5d76566d203fd62fe` |
| `evidence/logs/toeplitz-inverse-01.log` | `c2f0c66cabde823aa45cf9c1340939a6f5c9c1a1f9f0b9bb48c9d83fb396b99d` |
| `.lake/build/lib/lean/MF21Restart/ToeplitzInverse.olean` | `1c425393d13621f8ded3de09a173ac9a6d476670ccb9734cd76f3aef92f29e0f` |
| `MF21Restart/MatrixInverseAlgebra.lean` | `c8875cd75561ef852fa151509ad848659a04fdc8d758c358861a8abe41fe95d3` |
| `MATRIX_INVERSE_ALGEBRA_STATEMENTS.md` | `9cd0f449de998bb7d558814a3a52eb0c607e4297c44021c224fc3205bb18a02b` |
| `evidence/logs/matrix-inverse-algebra-02.json` | `45c5343e24049ab439b80cf22f45294cbac483f7f40bcb0db28fbe7a0fff7f00` |
| `evidence/logs/matrix-inverse-algebra-02.log` | `bf45f8662838aec3a47b518f131db5834f57c6406db717cfdff4d07cc8da164c` |
| `.lake/build/lib/lean/MF21Restart/MatrixInverseAlgebra.olean` | `54999a411e4a3ba91614d601e65754b823d1cc1d0dca283fac4d9575a1b9ffdb` |

Every hash above was independently recomputed. The two successful JSON
records match the corresponding current source/log/output triplets,
record exit_code=0 and source_unchanged=true, and specify
`LEAN_NUM_THREADS=1` and `lake env lean -j1 -M4096 -o <output> <source>`.
Each successful log has four standard-only axiom reports, restricted to
`propext`, `Classical.choice`, and `Quot.sound`.

The earlier MatrixInverseAlgebra01 record is a failed development run,
with a different source hash and missing real-number import. Its partial
printed output is not treated as proof evidence. The approval concerns
the source-matched successful 02 record, and ToeplitzInverse01.

## Algebra, normalization, and index audit

1. **The factors are literal finite matrices.** At
   `ToeplitzInverse.lean:14–20`, the inverse diagonal uses the reciprocals
   of the actual Pochhammer values at i.val+1. The candidate is exactly
   `P*B*W_inverse*B.transpose*P`, with both outer diagonal factors P,
   and the second triangular factor transposed. The definitions do not
   refer to the desired inverse or to an assumed kernel limit.

2. **Every diagonal reciprocal is legitimate.** Lines 22–31 prove
   strict positivity of the rising factorial at the positive real
   argument i.val+1, for every natural order r, including r=0.
   These conclusions discharge every nonzero-diagonal premise; no zero
   Pochhammer value at index zero has been silently inverted.

3. **The generic matrix algebra preserves multiplication order.**
   `MatrixInverseAlgebra.lean:15–27` proves both reciprocal-diagonal
   identities entrywise. Lines 29–48 assume precisely
   `R*P=1`, `T*B=1`, `B*T=1`, `W*V=1`, and `T.transpose*W*T=P*A*P`.
   In `A*(P*B*V*B.transpose*P)`, insert R*P on the left, replace P*A*P
   by the weighted factorization, cancel T*B and W*V, and then cancel
   `T.transpose*B.transpose=(B*T).transpose`. The remaining R*P is one.
   No matrices are commuted, and no diagonal or symmetry premise is
   illicitly used for this generic argument. Lines 50–56 use the true
   finite-matrix inverse theorem, not a new definition of inverse.

4. **The application discharges all five finite hypotheses.**
   `ToeplitzInverse.lean:26–38` supplies the actual integral-defined
   `toeplitz m n`, its actual rising-factorial diagonals, and the exact
   two-sided inverse triangular matrices. The last input is the proved
   actual identity `T.transpose*W*T=P*A*P`; there is no remaining
   factorization, invertibility, positivity, or spectral assumption in
   the public right-inverse theorem beyond m>=1. Any n is allowed.

5. **This is Mathlib's actual nonsingular inverse.** Lines 40–42 derive
   `(toeplitz m n)⁻¹=manuscriptFiniteInverse m n` from the established
   `A*G=1` using `Matrix.inv_eq_right_inv`. The pinned library proves
   this theorem via finite-square-matrix one-sided inverse equivalence;
   it is not a pseudoinverse or an assumed equality. The empty n=0
   matrix is included consistently, while all nonempty dimensions have
   an actual right inverse without an extra determinant hypothesis.

6. **The finite sum has the correct common upper index.** Lines 44–71
   expand the matrix product to
   `P_i*P_j*sum_k B_ik*B_jk/W_k`. Thus both conditions are `i<=k` and
   `j<=k`, exactly k>=max(i,j); the second one is not accidentally
   reversed by the transpose. The denominator is order 2m at k.val+1.
   The two binomial upper indices are
   `m-1+(k.val-i.val)` and `m-1+(k.val-j.val)` and are used only in the
   guarded branch where the differences are genuine nonnegative
   offsets. For every other k at least one triangular entry is zero.
   Both P factors are outside the sum with the correct order m.
   On i=j the square binomial term is retained; no diagonal-only or
   large-index restriction appears in the theorem.

As direct convention checks, for m=1,n=1 the candidate is 1/2, the
inverse of the actual scalar Fourier coefficient 2. For m=2,n=1 it is
`(2!)^2/4!=1/6`, the inverse of the central coefficient 6. These symbolic
checks confirm the i+1 shift and factorial normalization; they are not
substitutes for the universal Lean proof.

## Source fidelity, dependency scope, and remaining work

The actual Fourier and matrix definitions remain unchanged in
`Definitions.lean`, SHA256
`35a74047a81a9b7526e9bf039880ca8f07ae33314e2b5b960ab254e02fca4b51`.
The assembly uses `TriangularInverse.lean`, SHA256
`07f55713eb4977c850e148c09943ef9cced5d75adc1b6d60362ecd40991ee319`,
with the separately compiled exact coefficient and inverse interfaces.

**Excluded from this reviewer's independent-authorship scope:**
`ToeplitzWeightedFactorization.lean`, SHA256
`ce4688dbb33b3482e6fc22315cc4b9cff3aa31fa491bfa018cd5f86e71d32a5e`,
and this reviewer's own WeightedBinomialInverse, FourierBinomialStencil,
and earlier Fourier proof internals. The present review checks their
exact statements as used here and the new assembly, but cannot constitute
independent review of those own-authored dependencies. That distinction
is material for any later claim about review of the complete inverse
route.

The unchanged manuscript `original-proof/solution.md`, SHA256
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`,
uses the known uniform inverse-kernel limit in (26), then (27)–(29).
This new component proves finite algebra toward that cited input; it
does not assume the limit or alter its original statement. The finite
formula is the known Duduchava–Roch route identified in
`INVERSE_KERNEL_RESEARCH.md`; no new discovery is claimed. Conversion
of the binomial factors to rising factorials and the uniform kernel
limit remain separate obligations, as the lock explicitly states.

A read-only scan of the 11-module project import closure found no
`sorry`, `admit`, custom axiom, unsafe declaration, `native_decide`, or
`Challenge` import. No numerical computation or dimension-dependent
verification is introduced. Comparator has not run, and neither a
uniform kernel limit nor MF-21's full Target is completed by this
component. No original-target count increases.
