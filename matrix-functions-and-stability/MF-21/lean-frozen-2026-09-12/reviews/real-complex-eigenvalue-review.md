# Independent real/complex eigenvalue bridge review

Verdict: **APPROVE** for the three declarations in
`MF21Restart/RealComplexEigenvalue.lean`, with the precise partial scope
below. I found no material mathematical or source-fidelity issue. The
statements match `ROOT_EIGENVALUE_BRIDGE_STATEMENTS.md` and the
eigenvalue-existence criterion following manuscript (13), lines 149–159.
This does not approve an equality of kernel dimensions, determinant-zero
multiplicities, phase indexing, or the complete MF-21 target.

I independently read the current proof and statement lock, the unchanged
shared definitions, `EigenvalueBridge`, `BoundaryToeplitz`, and the
convolution proof in `ToeplitzRecurrence`. I checked the actual Mathlib
characteristic-root/eigenvector statements and the Hermitian characteristic
root multiset. Earlier independent reviews separately cover the recurrence
basis, finite ghost extension, and Fourier recurrence ingredients; their
scope is not expanded by assuming the final conclusion here. The pinned
referee rubric has SHA256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Real characteristic roots and complex eigenvectors

`real_matrix_charpoly_root_iff_complex_eigenvector` (lines 18–42) is valid
for every real square matrix and real spectral parameter. Its coefficient
map is the injective ring homomorphism `Complex.ofRealHom`.
`Matrix.charpoly_map` and `Polynomial.isRoot_map_iff` give the equivalence
between the real characteristic root and its complex image; injectivity
is actually supplied. The second step uses Mathlib's proved
`Module.End.hasEigenvalue_iff_isRoot_charpoly`, then converts between the
eigenspace statement and the literal nonzero-vector equation for
`Matrix.mulVecLin`. The nonzero condition occurs in both directions.

No Hermitian hypothesis is required for this statement, no eigenvector or
kernel equivalence is assumed, and no conclusion about nonreal roots is
made. The generality in the lock is appropriate. At `n=0`, the
characteristic polynomial is 1 and the only vector is zero, so both sides
are false; there is no missing nonempty-dimension assumption. A repeated
characteristic root causes no difficulty because the statement concerns
existence, not algebraic or geometric multiplicity.

## Actual sorted list, matrix, and boundary determinant

The underlying matrix is the unchanged `Definitions.toeplitz` (lines
20–25): the normalized Fourier integral with coefficient index `i-j`.
Hermitian symmetry is proved from evenness, not assumed. The list at lines
38–39 sorts the actual Hermitian eigenvalue multiset in increasing order.
It preserves repeated entries. `eigenvalue` (lines 44–53) is one-based,
using list position `j-1`, and is only used with `1 ≤ j ≤ n`.

`EigenvalueBridge.eigenvalue_index_iff_mem_orderedList` (lines 15–29)
uses the actual list length n and reconstructs a bounded index as `i+1`.
Both endpoints, `j=1` and `j=n`, are included. Its characteristic-root
corollary (lines 31–37) uses monicity to justify polynomial root membership
and the actual Hermitian root multiset. The totalized value zero outside
the published index interval is never admitted. With `n=0`, the bounded
index existential and list membership are both false, as required.

`eigenvalue_index_iff_boundaryDeterminant_zero` (lines 45–54) composes
these exact equivalences with the new scalar-field bridge and the proved
`BoundaryToeplitz` criterion, in the correct directions.
`mem_orderedEigenvalueList_iff_boundaryDeterminant_zero` (lines 57–65)
is the equivalent list-membership form. Neither changes the spectral
parameter, matrix, coefficient normalization, or boundary definition.

I checked the relevant finite-matrix identification rather than treating
it as an unexplained imported criterion. `ToeplitzRecurrence` lines 31–36
explicitly changes the convolution coefficient `a_(j-k)` into the matrix
coefficient `a_(k-j)` using evenness. Its sum reindexing handles only
nonzero terms, establishes the guarded natural-subtraction bounds, and
uses proved Fourier support to supply every nonzero matrix term.
`BoundaryToeplitz` evaluates the exact recurrence at `k<n` and its central
sample at `k+m`; `zeroGhostExtension_middle` identifies that sample with
`v k`. Both implications use this equality. Thus no transpose or shift
convention is hidden in the final composition.

The boundary matrix has upper exponents `0,...,m-1` and lower exponents
`n+m,...,n+2m-1`, matching (13) exactly. The hypotheses provide 2m distinct
nonzero roots of the actual Laurent spectral equation. They suffice for
the order-2m geometric recurrence basis; an extra completeness assumption
is unnecessary. They do not assume determinant singularity or any
Toeplitz eigenvalue. The `1 ≤ m` condition is exactly the existing
recurrence-normalization condition. It avoids the order-zero degeneracy
where the central and terminal terms coincide.

As a concrete edge check, when `n=0` the boundary exponents together are
`0,...,2m-1`, so the matrix is Vandermonde and nonsingular under the
injectivity hypothesis, agreeing with the empty eigenvalue list. When
`m=1,n=1`, the interior matrix is `[2]`; roots `i,-i` at `lam=2` make the
boundary determinant zero. At coalescing spectral endpoints the actual
manuscript root list is not injective, so this theorem correctly does
not assert that the distinct-root criterion applies there.

## Remaining work and trust scope

This module establishes the exact existence bridge from the published
sorted eigenvalue accessor to a supplied characteristic-root boundary
determinant. Membership equivalence alone does not count zero orders,
prove simplicity, identify a phase integer with the index j, construct
the specific smooth root list, or normalize the determinant into
`sin(F_n)+E_n`. It also does not prove the stronger equality of kernel
dimensions stated in the manuscript. Those are separate mathematical
obligations; they are not contradicted by the present proof.

No custom axiom, placeholder, `native_decide`, unsafe shortcut, numerical
certificate, or large finite computation occurs in the reviewed new
module or the three directly inspected bridge modules. Existing Mathlib
polynomial and linear-algebra APIs are reused. The unused simp argument
warning in the earlier eigenvalue-bridge log is optional cleanup only;
it does not alter the theorem or proof trust.

The coordinator reported actual local `real-complex-eigenvalue-01` exit
0 for the exact source hash below. I read that log: all three declarations
print only `[propext, Classical.choice, Quot.sound]`. I also read the
existing eigenvalue-bridge-01 and boundary-toeplitz-01 logs, whose
corresponding declarations print the same standard axiom set. I ran no
Lean compiler or other test, and no Comparator or GitHub workflow was
run as part of this review. The coordinator retains the serialized local
commands and run records. This approval is an independent mathematical
and source review, not an independent compiler execution or a completed
original-problem count.

## Source and evidence hashes

| File | SHA256 |
|---|---|
| `MF21Restart/RealComplexEigenvalue.lean` | `86f2f2cb01dea730e5c6c2042fa52652c25f0d99a683c6ffaef12bb404c8f2a0` |
| `ROOT_EIGENVALUE_BRIDGE_STATEMENTS.md` | `5f02ef317a1404f54af70a66e02ec47763c7475821b7daab10f84e112acc3df6` |
| `MF21Restart/EigenvalueBridge.lean` | `e07040bc9e98995f4c6ead6d7d9bbd3754c68acc36c71b115e4e117453c4c811` |
| `MF21Restart/BoundaryToeplitz.lean` | `0e902d88e92b2609b159df07b118a7a4973607f2346687c6734ec47947369b19` |
| `MF21Restart/ToeplitzRecurrence.lean` | `491d34f1776dcc4428b4b90071cdba5f1b8054538ee81876a6b046cafae04b22` |
| `MF21Restart/Definitions.lean` | `35a74047a81a9b7526e9bf039880ca8f07ae33314e2b5b960ab254e02fca4b51` |
| `evidence/logs/real-complex-eigenvalue-01.log` | `3645a2590378a3b5a1977ce3fb46c45f112075743e3e662861d138690c9e4d9a` |
| `evidence/logs/eigenvalue-bridge-01.log` | `8a28818aad6e8d4114fd6c3e35a7d111627f7944c58806f5cdb8fa169eba9491` |
| `evidence/logs/boundary-toeplitz-01.log` | `333dd59753dd220426d93b4d32f3661cfe69d15b3b50e5805e53854f76dacfa6` |
| `/private/tmp/mf21-solution.md` | `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa` |
