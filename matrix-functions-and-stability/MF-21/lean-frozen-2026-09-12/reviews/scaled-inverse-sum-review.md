# Independent review: exact rescaled finite inverse

Verdict: **APPROVE** `scaled_toeplitz_inverse_eq_sum` at the exact hash
below. The identity concerns the actual Toeplitz matrix inverse and
retains the correct one-based grid offsets, factorial normalization,
and power of h. It is a finite identity and makes no convergence claim.

Reviewer: `/root/mf21_restart_lean_audit`, 20 September 2026. The
coordinator authored the module. The reviewer edited no source and
ran no compiler. The pinned referee standards have SHA256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Exact source and actual local evidence

| Artifact | SHA256 |
|---|---|
| `MF21Restart/ScaledInverseSum.lean` | `5e74e548d82d7a1d463dd278164c9821c51d2a462fc089cb6fb7ce09c8b5e197` |
| `SCALED_INVERSE_SUM_STATEMENTS.md` | `af98fd50c91f8acc4a2cf25b18a65cecfe5392de09f04fd9ce041d1826603ca8` |
| `evidence/logs/scaled-inverse-sum-01.json` | `d3e6efb9daac75bc27f8be148a6a9b5a3a7ee417283db83f835b12bd9f9d2d51` |
| `evidence/logs/scaled-inverse-sum-01.log` | `5a2f8b0de4ca89292314128212b1dcfa92c4954c85ec3cf09b56108711a32f50` |
| `.lake/build/lib/lean/MF21Restart/ScaledInverseSum.olean` | `36bbf5cadeb40bb4552f4a07534de097cc53a980e79073b567743235c8e97e0b` |

The reviewer independently recomputed all five hashes and matched the
current source, log, and output to the actual 01 record. It records
`exit_code=0`, `source_unchanged=true`, `LEAN_NUM_THREADS=1`, and
`lake env lean -j1 -M4096 -o
.lake/build/lib/lean/MF21Restart/ScaledInverseSum.olean
MF21Restart/ScaledInverseSum.lean`. The sole printed theorem depends
only on `propext`, `Classical.choice`, and `Quot.sound`. The redundant
final `ring` produces harmless unreachable/unused-tactic warnings;
there is no error or missing proof. No Comparator run is claimed.

## Mathematical findings

1. The public type at lines 12–18 matches the prior lock. It allows
   all natural n, positive order m, every nonzero real h, and actual
   indices i,j:Fin n. The left side is
   `h^(2*m-1)*(toeplitz m n)⁻¹ i j`; the right is h times the guarded
   sum of the concrete finite kernel integrand at
   `h*(i.val+1),h*(j.val+1),h*(k.val+1)`. Thus the later choice h=1/n
   has the manuscript's scaling n^(1-2m). No n+2 scaling is silently
   substituted at this finite-kernel stage.

2. Lines 20–27 use m>=1 to identify m=(m-1)+1 and the two needed
   exponents: 2m=2(m-1)+2 and 2m-1=2(m-1)+1. This avoids an
   invalid natural subtraction at m=0. At m=1 the two order-zero
   factors and 0! are retained correctly. The equality holds for
   negative h as well: h is only cancelled after nonzeroness is
   supplied, and no false positivity premise about h is used.

3. Lines 28–41 start from the proved actual inverse entry formula,
   distribute the finite sums, and preserve both guards i<=k,j<=k.
   Natural subtraction is converted to real subtraction only inside
   those guards. In each contributing term,
   `h*(k-i+1)=h*(k+1)-h*(i+1)+h`, precisely the integrand's t-x+h
   shift, and similarly for y. No lower or upper summation endpoint
   is dropped. With n=0 there are no index pairs; no matrix entry or
   division by n is asserted.

4. Lines 42–50 establish the factorial and positive integer-start
   denominator as nonzero, use the exact scaled-rising identity in
   every rising factor, and cancel h using hh. The numerator scaling is
   h^(4m-2), the denominator scaling h^(2m), and the external h
   supplies total h^(2m-1). The original inverse's factorial square
   remains the integrand's factorial square. The false-guard branch
   is exactly zero on both sides at line 51.

## Independence, trust and scope

The recursive project import closure contains 14 source files,
including this module, with no `sorry`, `admit`, custom `axiom`,
`unsafe`, or `native_decide` marker. Challenge is not imported. This
review covers the named coordinator-authored equality and its use of
the existing APIs. It does not independently review this reviewer's
own WeightedBinomialInverse, FourierBinomialStencil, or
ToeplitzWeightedFactorization proof internals. The previous independent
reviews of ToeplitzInverse, InverseKernelEntries and ScaledRising give
their separately recorded scopes; known Duduchava–Roch attribution
for the finite inverse remains unchanged.

The unchanged manuscript SHA256 is
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`.
This identity supplies a finite prerequisite for lines 312–325,
equations (26)–(27). The Riemann-sum limit, uniformity at changing
indices, reflection and endpoint conventions remain separate. No
kernel limit, trace limit, or completed original MF-21 Target is
proved by this theorem. No completed-target count changes. No
material issue was found.
