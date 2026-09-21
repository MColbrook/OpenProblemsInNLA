# Independent boundary and finite recurrence review

Verdict: **APPROVE** for mathematical/source fidelity of the reviewed recurrence criteria. This is the actual recurrence/kernel connection in the paragraph after manuscript (13), before specialization to the Fourier eigenvalue equation. No full eigenvalue criterion, nullity equality, root construction, spectral indexing, determinant normalization, or asymptotic MF-21 conclusion is approved here.

I read both proof modules and their locks, the exact imported boundary-matrix definition and recurrence basis, and Mathlib's recurrence equation, constructed solution, and uniqueness API. The coordinator reports `boundary-recurrence-02` exit 0; I read its two standard-axiom outputs. `FiniteRecurrence.lean` has the explicit interval-membership elaboration fix below; the coordinator subsequently reported `finite-recurrence-02` exit 0, and I read its two standard-axiom reports against the unchanged reviewed source. I ran no Lean or other compiler, Comparator, or GitHub workflow. These actual local results support the source-faithfulness/mathematical review and are not claimed as independent compiler reruns.

## Boundary determinant criterion

`BoundaryExpansion.boundaryMatrix` uses row exponent r for r<m and n+r for r≥m. Its row equivalence identifies r=k and r=m+k. Thus `BoundaryRecurrence.boundary_mulVec_upper/lower` (lines 15–25) computes exactly the sums at the shifted ghost indices k and n+m+k, for 0≤k<m. `boundary_mulVec_zero_iff_ghosts` (lines 27–46) covers every row using the actual row equivalence; it is not a partial set of constraints.

`boundaryDeterminant_zero_iff_recurrence_ghosts` (lines 50–87) concerns the actual square boundary matrix and recurrence `LinearRecurrence.mk (2*m) a`. Its hypotheses are an injective list of 2m nonzero characteristic roots. The determinant-zero direction obtains a nonzero coefficient vector from the matrix kernel theorem, proves its geometric sum solves the recurrence, and proves the resulting sequence nonzero using Vandermonde uniqueness. The converse uses the separately proved geometric basis, proves its coefficients cannot all vanish, and applies the same actual matrix-kernel criterion. No nontrivial kernel or dimension assertion is assumed.

The list length equals the recurrence order, all characteristic-root equations are explicit, and no eigenvalue or asymptotic hypothesis appears. Nonzero roots are natural for the manuscript's root list. At shift zero the coefficient-uniqueness argument could in fact use only injectivity; the stronger nonzero-root input comes from reuse of the shared arbitrary-shift lemma and is optional generality polish, not a source-fidelity failure. The concrete application must still construct this root list and identify its characteristic polynomial.

## Finite extension and restriction

`FiniteRecurrence.mkSol_eq_of_finite_recurrence` (lines 12–33) proves actual agreement through t<N+d from recurrence equations at all k<N. Strong induction handles t<d by the initial-data theorem and t≥d with k=t-d; every recursive index k+i is strictly smaller than t. The endpoint t<N+d is exact, not off by one. This is derived from the recurrence, not a assumed extension property.

`zeroGhostExtension` (lines 35–36) embeds the vector at m,...,m+n-1 and is zero elsewhere. Natural subtraction t-m is used only in the branch with m≤t and t<m+n; the Fin n membership proof is supplied from those facts. The typed `hinterval` at lines 62–63 merely makes that conjunction explicit for `dif_pos`; it changes no statement or branch condition. The reconstruction helper (lines 50–70) uses the two ghost ranges and middle interval to prove agreement on every t<n+2m.

`finite_recurrence_iff_ghost_solution` (lines 72–119) has the locked existential equivalence. In the forward direction, the full solution is Mathlib's unique `mkSol` from the initial 2m extension values. The finite extension theorem makes it agree on the entire required block, transfers both ghost conditions, and transfers nonzeroness from the middle vector. In the converse, v(i)=u(m+i) gives the middle vector and the reconstruction helper transfers each recurrence equation. If that vector were zero, the first 2m sequence values would all vanish; actual recurrence uniqueness then forces u=0. Thus the nonzero restriction is proved, not obtained from a claimed nullity equality.

For k<n, the largest index used is k+2m≤n+2m-1, so every equation lies in the reconstructed block. The proof also works when n<m. Degenerate n=0 gives false on both nonzero-existence sides; order 0 likewise permits only the zero full solution, and the finite equations force the middle vector zero. No positivity assumption was added to avoid these cases.

## Limits and trust

The theorem types match `BOUNDARY_RECURRENCE_STATEMENTS.md` and `FINITE_RECURRENCE_STATEMENTS.md`. Their conjunction supplies an existence criterion between a boundary-matrix kernel and a nonzero finite recurrence solution after using the same recurrence coefficients and roots. It does not yet identify that finite recurrence with `(A_n-λI)v=0`; the Fourier-to-recurrence coefficient/sign and endpoint normalization bridge remains explicit work. It also does not establish equality of kernel dimensions, which would require the linear equivalence maps or an equivalent argument beyond this existential conclusion.

The modules introduce no axiom, placeholder, unsafe shortcut, or generic assumption equivalent to the desired criterion. Existing Mathlib recurrence construction, uniqueness, Vandermonde and matrix-kernel APIs are reused. No numerical certificate or large computation is needed. The initial failed boundary01 artifact is not accepted; boundary02's observed standard axiom outputs apply to the frozen source below. FiniteRecurrence02's log prints only `[propext, Classical.choice, Quot.sound]` for both public theorems; the coordinator reported the actual exit 0. Neither module has a Comparator result in this review.

## Reviewed source and evidence hashes

| File | SHA256 |
|---|---|
| `MF21Restart/BoundaryRecurrence.lean` | `51605ff0487f4abd102ab9e6e755513adcbbf6c4df10007360227c3a3cf12f44` |
| `MF21Restart/FiniteRecurrence.lean` | `a252b76405c506b2b850e288c41769083267a23a4e454c424096a6002e4db39a` |
| `MF21Restart/BoundaryExpansion.lean` | `bc873ac5a5cb569d3dda0bc3b6ecf623e09d326f0d82cd613fdc3149c24a3979` |
| `MF21Restart/RecurrenceBasis.lean` | `ef4a5d7bbbb5db6e849ec6dbbc9289bda98300d7e1a7f78e47c26fd61457454b` |
| `BOUNDARY_RECURRENCE_STATEMENTS.md` | `7c591f488e0dd73105ca1b68eba679e9c19fd3588e5a8b45617931bd3a3c1b0e` |
| `FINITE_RECURRENCE_STATEMENTS.md` | `664f1825be99c2dfa19d7bec62fe098ea1135a12b7681403e88577fca2f7554b` |
| `original-proof/solution.md` | `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa` |
| `reviews/REFEREE_STANDARDS.md` | `e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1` |
| `evidence/logs/boundary-recurrence-02.log` | `8b4bbe8c041d37286c9439f59debfc7e1ec64c4c42c6970008b3552cec3c76e6` |
| `evidence/logs/finite-recurrence-02.log` | `0e0071373d95c216d981e7f6da9cc80bd9da7cf57807b21623b6e20a821c4ad5` |
