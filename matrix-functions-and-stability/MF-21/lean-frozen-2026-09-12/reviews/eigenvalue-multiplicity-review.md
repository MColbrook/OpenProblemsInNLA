# Independent sorted eigenvalue multiplicity review

Verdict: **APPROVE**, for the two public results in
`EigenvalueMultiplicity.lean`. They establish that multiplicity in the
unchanged sorted real eigenvalue list equals the actual complex eigenspace
dimension, and that dimension one gives a unique bounded one-based index.
The module does not prove its dimension-one premise or locate an eigenangle.

Reviewer: `/root/mf21_restart_lean_audit`, 20 September 2026. I did not
author or edit this module. I read its complete source, exact statement
lock, frozen definitions, existing index bridge, manuscript Lemma 4, and
the relevant pinned Mathlib spectral, root-multiplicity, coordinate, and
finite-count lemmas. I ran no compiler. The pinned referee standard has
SHA-256 `e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Exact inspected sources and execution artifacts

Paths are relative to `MF21-restart`.

| Path | SHA-256 |
| --- | --- |
| `MF21Restart/EigenvalueMultiplicity.lean` | `d2cd938bd1fbbf405f8c2645d38224cfbbf66df058318d11eababe2ecec71bd1` |
| `EIGENVALUE_MULTIPLICITY_STATEMENTS.md` | `2e82a5c33cb5761514b6dd8c435596b6c57aae1f9548745f128f4fe4e6a00ab8` |
| `MF21Restart/Definitions.lean` | `35a74047a81a9b7526e9bf039880ca8f07ae33314e2b5b960ab254e02fca4b51` |
| `MF21Restart/EigenvalueBridge.lean` | `e07040bc9e98995f4c6ead6d7d9bbd3754c68acc36c71b115e4e117453c4c811` |
| `original-proof/solution.md` | `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa` |
| `evidence/logs/eigenvalue-multiplicity-02.json` | `422403064c0d37c8ef5b49bc2b99f8eddfda5b5705d6f0513779c3f4465a22fb` |
| `evidence/logs/eigenvalue-multiplicity-02.log` | `6f1f6c386111f67de040c56472b68fbd9c1888ca5ce0abb4137e78004ef08d3b` |
| `.lake/build/lib/lean/MF21Restart/EigenvalueMultiplicity.olean` | `d3cb03b88c0a29ea650443a2ba2c6e6f0c4f92c1bbe470c2781fee45a5480d15` |

The individual record reports an actual local run from epoch
`1789936473.298172` to `1789936480.173992`, equivalently
`2026-09-20T20:34:33.298172+00:00` through
`2026-09-20T20:34:40.173992+00:00`, with command

```text
lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/EigenvalueMultiplicity.olean MF21Restart/EigenvalueMultiplicity.lean
```

It records exit code 0 and unchanged source. I rehashed the source,
log, and compiled artifact; all three exactly match their recorded
hashes. Both public axiom reports list only `propext`, `Classical.choice`,
and `Quot.sound`. The sole warning is an unused simp argument. This is
local execution evidence, not an independent compiler run by this
reviewer or a GitHub Comparator result.

## Statement identity and mathematical content

The public statement at lines 79–84 counts `lam` in
`orderedEigenvalueList m n`, not in a newly chosen or distinct-value
list. The list's frozen definition at `Definitions.lean:38–42` sorts all
n Hermitian eigenvalues **with their repetitions**. Its right-hand side
is the complex dimension of the literal eigenspace of
`((toeplitz m n).map Complex.ofReal).mulVecLin` at `(lam:ℂ)`. The
matrix remains the integral-defined Toeplitz matrix from lines 20–25
of the definitions. Neither simplicity nor an assumed dimension formula
is a hypothesis of this equality.

The result at lines 112–117 has exactly the locked dimension-one
hypothesis and concludes
`∃! j:ℕ, 1<=j ∧ j<=n ∧ eigenvalue m n j=lam`.
The two index bounds are part of the uniquely satisfied predicate. They
exclude the accessor's totalized zero at j=0 and j>n. The index denotes
the published one-based position, using the frozen shift j−1. No
zero-based replacement or additional unproved simplicity hypothesis is
present.

The source is stronger than needed with respect to m and n: it permits
all natural values. At n=0 the list is empty and the eigenspace of the
zero-dimensional operator has dimension zero, so the first statement
is correct and the second premise is impossible. For a repeated
eigenvalue the first theorem counts every occurrence; the second theorem
does not apply until the dimension is actually one. For values absent
from the spectrum, both sides of the count theorem vanish. These cases
do not produce a vacuous general theorem or contradict the manuscript.

## Coordinate and spectral proof checks

The private helper at lines 21–48 uses the actual complex-linear
equivalence from Euclidean-space coordinates to ordinary function
coordinates. At line 28 it checks that this equivalence intertwines
`A.toEuclideanLin` and `A.mulVecLin`. It proves equality with the comap
of the target eigenspace, then restricts the equivalence to the subspaces.
Consequently the dimension comparison is over **ℂ** on both sides; it
does not confuse complex dimension with twice that dimension over ℝ.

The private Hermitian lemma at lines 52–77 identifies the Euclidean
operator's characteristic polynomial with the actual matrix charpoly.
Mathlib's proved symmetric-operator spectral theorem writes its roots
as the multiset of eigenvalues and identifies the number of indices at
each eigenvalue with the eigenspace dimension. The filter equality at
lines 67–74 only reverses equality's orientation after `count_map`.
The coordinate helper then yields the matrix `mulVecLin` eigenspace.
No diagonalization, characteristic factorization, or algebraic-equals-
geometric multiplicity fact is assumed in this project helper.

At lines 86–90 the sorted real list is identified as a multiset with the
real matrix's charpoly roots. The explicit `List.mergeSort_perm` step
preserves multiplicities during sorting; merely proving membership
would not suffice here. Lines 91–92 transport the already proved
Hermitian property to the complexified matrix.

The chain at lines 94–108 turns a real list count into real polynomial
root multiplicity, preserves that multiplicity under the injective
real-to-complex ring map, uses the literal `Matrix.charpoly_map`, and
then applies the complex Hermitian lemma. The cast and map are the
actual `Complex.ofRealHom`; there is no hypothesis that an arbitrary
matrix has its real and complex multiplicities equal. Mathlib's
`Polynomial.eq_rootMultiplicity_map` requires precisely the proved
injectivity used here.

## One-based uniqueness and manuscript scope

Lines 119–124 use the actual length-n list as a `List.Vector` and
identify its occurrence count with the cardinality of the finite set
of matching zero-based positions. Cardinality one supplies a unique
position i. Lines 127–129 return i+1, using i<n for the upper bound
and the frozen accessor equation for its value.

For any competing published index j, lines 130–139 use `1<=j<=n` to
construct `k=j−1 : Fin n`. The accessor equation shows that k belongs
to the same singleton set. Uniqueness of the finite position gives
j−1=i and hence j=i+1. Thus the conversion is exact at both j=1 and
j=n, and the accessor's out-of-range values never participate.

The theorem closes the implication from complex geometric dimension
one to a single occurrence in the actual eigenvalue list, used in
`original-proof/solution.md:239`. The algebraic multiplicity identity is
derived in the proof rather than postulated. It does not show which
phase interval yields that position, prove monotonic phase counting,
or supply the dimension-one input. Those remain separate analytic and
boundary-determinant obligations.

## Trust and verdict limits

No `sorry`, `admit`, custom axiom, unsafe shortcut, `native_decide`,
Challenge import, legacy formalization import, or numerical certificate
appears. The source reuses the pinned spectral and root-multiplicity
APIs and performs symbolic finite-dimensional reasoning. Its exact
types match the lock, and no material correctness or source-fidelity
change is requested.

This review approves the two stated ingredients only. It is not
approval of a complete Target theorem, a claim that the outstanding
analytic hypotheses have been discharged, or a Comparator verification.
No additional completed original target is counted.
