# Independent boundary and spectral bridge review

Verdict: **APPROVE**, for the exact partial statements in
`BoundaryToeplitz.lean`, `EigenvalueBridge.lean`, and the previously reviewed
`ToeplitzRecurrence.lean`. No complete MF-21 target is certified here.

Reviewer: `/root/mf21_restart_lean_audit`, 20 September 2026. I did not author
or edit these three modules. I inspected their statement locks and proof
bodies, the finite-extension and boundary-recurrence dependencies, and the
local logs listed below. I launched no compiler. I authored
`FourierStencil`, `FourierLaurent`, `FourierEndpoint`, `FourierRecurrence`,
and `FourierRecurrenceEquation`; this is **not** an independent review of
those modules. Their exact applications in the new bridge are checked
here, with their proofs treated as dependencies requiring separate review.

Review standard: `/Users/georgestepaniants/Research/project/lean-verification/REFEREE_STANDARDS.md`,
SHA-256 `e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Exact source scope

All project paths are relative to `MF21-restart`.

| Path | SHA-256 |
| --- | --- |
| `MF21Restart/BoundaryToeplitz.lean` | `0e902d88e92b2609b159df07b118a7a4973607f2346687c6734ec47947369b19` |
| `BOUNDARY_TOEPLITZ_STATEMENTS.md` | `54a85e2a75ebd55148af53992ddcfeef888f5b4d07ec6499d50f7bb97bb1296f` |
| `MF21Restart/EigenvalueBridge.lean` | `e07040bc9e98995f4c6ead6d7d9bbd3754c68acc36c71b115e4e117453c4c811` |
| `EIGENVALUE_BRIDGE_STATEMENTS.md` | `bc7579f4c07241c62c70f3af3d4c58628fe134cf24fe8eb1b93bc7187715d4f0` |
| `MF21Restart/ToeplitzRecurrence.lean` | `491d34f1776dcc4428b4b90071cdba5f1b8054538ee81876a6b046cafae04b22` |
| `TOEPLITZ_RECURRENCE_STATEMENTS.md` | `c06f9f9c8acdde1c65956b7ccbf16c8e30c6bb96e3c8ee5c8dfc2f718ab55143` |
| `MF21Restart/BoundaryRecurrence.lean` | `51605ff0487f4abd102ab9e6e755513adcbbf6c4df10007360227c3a3cf12f44` |
| `MF21Restart/FiniteRecurrence.lean` | `a252b76405c506b2b850e288c41769083267a23a4e454c424096a6002e4db39a` |
| `MF21Restart/RecurrenceBasis.lean` | `ef4a5d7bbbb5db6e849ec6dbbc9289bda98300d7e1a7f78e47c26fd61457454b` |
| `MF21Restart/BoundaryExpansion.lean` | `bc873ac5a5cb569d3dda0bc3b6ecf623e09d326f0d82cd613fdc3149c24a3979` |
| `MF21Restart/FourierRecurrenceEquation.lean` | `49d55d4312ac773733627b284f6319dd7c45319b24a6cbebf5914b280e78eb7d` |
| `MF21Restart/Definitions.lean` | `35a74047a81a9b7526e9bf039880ca8f07ae33314e2b5b960ab254e02fca4b51` |
| `original-proof/solution.md` | `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa` |

The earlier report `reviews/toeplitz-recurrence-review.md` remains applicable
to the unchanged convolution source and lock. Its integer-sign and finite
sum reindexing checks were also checked against the new bridge.

## Boundary determinant and actual Toeplitz operator

1. `BoundaryToeplitz.lean:16–22` exactly implements its lock: for `m >= 1`,
   arbitrary natural `n`, complex `lam`, and `2*m` distinct nonzero complex
   numbers satisfying `(2-w-w⁻¹)^m = lam`, singularity of the concrete
   boundary matrix is equivalent to a nonzero eigenvector of the
   entrywise complexification of the unchanged integral-defined Toeplitz
   matrix. No determinant criterion, eigenvector, Fourier support, or
   recurrence representation is assumed in the theorem's hypotheses.

2. Lines 23–25 select exactly the concrete `fourierRecurrence m lam`
   coefficients. The characteristic-root premise used by the abstract
   recurrence basis is derived from each supplied Laurent equation using
   `fourierRecurrence_charPoly_isRoot`. The `LinearRecurrence.mk` instance
   in that application has the same order and coefficients; there is no
   change to an arbitrary recurrence with an assumed connection.

3. Lines 26–29 compose the equivalences in the correct direction:
   boundary determinant zero iff a nonzero full recurrence solution with
   both ghost blocks, then iff a nonzero finite vector satisfying the
   normalized recurrence. In `BoundaryRecurrence.lean:50–87`, the
   geometric basis supplies the full solution and the Vandermonde
   uniqueness argument preserves nonzeroness. The two row groups at
   lines 15–46 exhaust the concrete boundary matrix and use precisely
   the exponents `k` and `n+m+k` from manuscript equation (13),
   `solution.md:149–159`.

4. `FiniteRecurrence.lean:12–33` proves finite agreement of the initial
   value solution by strong induction, rather than assuming global
   continuation of a finite vector. Lines 72–119 use this agreement in
   both directions and prove nonzeroness after extension/restriction.
   A supposedly nonzero full solution with zero interior and zero ghosts
   would have all its first `2*m` values zero, and recurrence uniqueness
   rules it out. Thus this argument does not introduce a spurious full
   solution supported beyond the finite region.

5. `BoundaryToeplitz.lean:31–48` converts each finite recurrence equation
   into the actual matrix row equation using
   `fourierRecurrence_equation_iff` and
   `zeroGhost_convolution_eq_toeplitz_mulVec`. The center `k+m` is exactly
   `v k`; the vector's nonzeroness is retained in each direction. The
   convolution identity already proves the needed sign change
   `t-m = -(k-j)` by the real Fourier coefficient's evenness
   (`ToeplitzRecurrence.lean:31–36`). It also retains both endpoint
   frequencies and justifies all natural subtractions before reindexing.

6. The conditions on the root list are genuine mathematical obligations,
   not contradictory hypotheses. They allow nonzero roots inside and
   outside the unit circle, as required by the manuscript. They exclude
   repeated-root endpoint cases. No construction or distinctness theorem
   for the manuscript's smooth root list is claimed. The `n=0` case is
   coherent: a nonzero vector in `Fin 0 -> ℂ` cannot exist, and the
   `2*m` consecutive boundary rows form a nonsingular Vandermonde matrix
   under the root assumptions.

This establishes the existential eigenvector criterion in the manuscript
paragraph following (13). The stronger statement in that paragraph that
the two kernels have equal dimensions is **not** proved by this theorem;
neither is an eigenvalue multiplicity or simplicity result. The statement
lock correctly claims only the existential equivalence.

## One-based enumeration and characteristic roots

1. `EigenvalueBridge.lean:11–29` derives the list length `n` from the
   unchanged Hermitian eigenvalue list, and proves equivalence with
   membership. In the reverse direction, the finite list index `i` is
   translated to the published natural index `i.val+1`. In the forward
   direction, `eigenvalue_in_range` uses `j-1`. Consequently the smallest
   eigenvalue (`j=1`) and largest (`j=n`) are both included.

2. The explicit bounds `1 <= j` and `j <= n` are retained in both public
   theorem statements. The totalized zero outside that range can never
   supply a witness. For `n=0`, both list membership and the bounded
   existential are empty; the characteristic polynomial is the nonzero
   constant 1 and has no roots. No extra `n>0` premise conceals that case.

3. Lines 31–37 identify the list with the roots of the actual real
   Toeplitz characteristic polynomial. `Matrix.charpoly_monic` justifies
   use of `Polynomial.mem_roots`; the Hermitian spectral theorem
   `roots_charpoly_eq_eigenvalues` supplies the precise multiset. Sorting
   does not remove repeated eigenvalues. This is an enumeration
   equivalence, not a simplicity or quantitative ordering assertion.

4. This module imports only `Definitions`. It does not rely on any
   asymptotic estimate, abstract eigenvalue array, legacy accessor, or
   target assumption. Both statements match the locked exact scope.

These two new modules do not yet directly state a single equivalence
between the complex boundary determinant and the one-based real accessor.
That composition additionally uses the ordinary complexification bridge:
for real `lam`, a nonzero complex eigenvector of the real matrix's
complexification iff the original real characteristic polynomial vanishes
at `lam`. This is an integration obligation, not a defect in either
reviewed theorem. The existing Mathlib `Matrix.charpoly_map` and
`Module.End.hasEigenvalue_iff_isRoot_charpoly` are relevant.

## Local evidence and limits

| Local log | SHA-256 | Inspected axiom reports |
| --- | --- | --- |
| `evidence/logs/boundary-toeplitz-01.log` | `333dd59753dd220426d93b4d32f3661cfe69d15b3b50e5805e53854f76dacfa6` | One public bridge theorem; standard axioms only |
| `evidence/logs/eigenvalue-bridge-01.log` | `8a28818aad6e8d4114fd6c3e35a7d111627f7944c58806f5cdb8fa169eba9491` | Both public equivalences; standard axioms only |
| `evidence/logs/toeplitz-recurrence-01.log` | `d785f7cc3fc2418f0026a5d52617e06c2f80d6623c303081b9c215583b6ac9c4` | The concrete convolution theorem; standard axioms only |

Here “standard axioms” means exactly `propext`, `Classical.choice`, and
`Quot.sound`. The coordinator reports actual serial local exit code 0 for
all three runs. I independently inspected the hashed logs and current
source bytes, without launching a compiler. The eigenvalue log's sole
warning is the unused simp argument `Function.comp_def`; it does not
affect the statement or proof. No reviewed source contains `sorry`,
`admit`, custom axioms, `unsafe`, or `native_decide`, and the visible import
chain uses neither the legacy project nor `Challenge` placeholders.

No GitHub Comparator run is certified by this report. In particular, this
review supplies no source-matched Comparator success claim, no proof of
the complete `Target`, and no completed-problem count. Root-list
construction, the quantitative determinant estimates, phase indexing,
asymptotic expansions, and the spectral trace link remain outside this
review's scope.
