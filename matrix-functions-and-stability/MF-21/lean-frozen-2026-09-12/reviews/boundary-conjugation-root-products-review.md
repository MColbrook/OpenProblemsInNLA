# Independent review: determinant conjugation and real root products

Verdict: **APPROVE**, for the scoped declarations below. This is an
independent source and mathematical review of coordinator-authored code,
not a new compilation or a GitHub Comparator result. The reviewer did not
run Lean. Eleven printed results are covered, together with their local
helpers; they are ingredients of manuscript (16) and (18), not the full
MF-21 target.

The pinned `REFEREE_STANDARDS.md` has SHA-256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.
The unchanged manuscript `/private/tmp/mf21-solution.md` has SHA-256
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`.

## Frozen scope

| File | SHA-256 |
| --- | --- |
| `MF21Restart/BoundaryConjugation.lean` | `0327b3279564ebc620e67657668f474bc2c3a23514df6e95cf74b159fb8bdc9c` |
| `BOUNDARY_CONJUGATION_STATEMENTS.md` | `60ec0c241b839f41ba384d0658734752c35e6ede9b288d32dd787217f8ec0351` |
| `MF21Restart/RootListProducts.lean` | `331f649581125568a45313aea57d79342c4362ae1efb4d0dad1f5ff64f91c75e` |
| `ROOT_LIST_PRODUCT_STATEMENTS.md` | `14bb7df399d047b7548576c54ab51fe984645777f711c03308c3c501282d4c72` |

Relevant imported local interfaces were also inspected:
`ConcreteBoundary.lean` SHA-256
`bde3c2195d13e981249f6eebf9691b05d1f186edad7aa7b9e72c133f911063f4`
and `BoundaryProductDecay.lean` SHA-256
`f9f9b6b0d5c8b8842049f91850a3cb6d4482747443c1448d1c1e325bdcd0d0e3`.
The reviewer authored an earlier version of the latter dependency; this
report does not claim a new independent review of that dependency itself.

## Source fidelity and proof audit

`BoundaryConjugation.lean:10–28` constructs the actual block equivalence
from `(R, (z,z⁻¹), O)` to the frozen `Fin (2*m)` order. Its conjugating
permutation reverses each of the two length-`m-1` lists and swaps the two
central positions. `rootConjugationPerm_sign` correctly cancels the two
identical reversal signs and retains the central swap's sign `-1`.
This avoids making either individual reversal even by assumption. The
equivalence's dimension equality genuinely uses `1 ≤ m`.

The four block-root helpers at lines 30–57 check the concrete indices,
including the exterior offset `m-1+2+i`. `characteristicRoots_conj`
(lines 64–102) uses the established root-parameter conjugacy and the exact
identity `m-(i+1)=rev(i)+1`; the unit pair is conjugated by the actual
complex exponential. These statements are valid for all real theta.
They require no distinctness or eigenvalue assumption, so degeneracy at
zero and at pi is harmless.

`manuscriptBoundaryDeterminant_conj` (lines 104–117) maps conjugation
through the actual determinant and through every integer power in the
actual boundary matrix. The resulting operation is a column permutation,
not a row permutation or a conjugate transpose. `Matrix.det_permute'`
and the proved sign then give `conj D = -D`. Its real-part corollary
(lines 119–123) is the real arithmetic consequence. This faithfully
implements manuscript line 213 for determinant (13), lines 151–156.
The allowed `n=0` case and endpoint determinants introduce no division
or nonzero premise.

`RootListProducts.lean:10–27` defines the literal lists of roots and their
reciprocals and proves their conjugate reversal. The `Fin (m-1)` domain
is empty when `m=0` or `m=1`; unrestricted conjugacy statements therefore
have the expected empty-list behavior rather than a contradictory
parameter hypothesis. For actual entries, `1 ≤ ell+1 < m` is derived
from membership in that domain.

`boundaryExteriorProduct_eq_prod_exteriorRootList` (lines 29–57) proves
the indexing identification using the injective image
`ell ↦ m+1+ell`. It neither drops multiplicities nor introduces an
independently postulated product. Conjugation invariance (lines 59–64)
then follows by reindexing the entire product under `Fin.revPerm`, and
the zero value (lines 66–69) follows from the actual roots' value one.

`boundaryExteriorProduct_re_pos` (lines 71–87) uses the already-proved
nonvanishing of the actual product, its reality, its global continuity,
and its value one at zero. If its real part were nonpositive at a
nonnegative theta, the intermediate value theorem on `[0,theta]` would
produce a zero. This proves the stated strict positivity for `m ≥ 2`
and `theta ≥ 0`, including theta zero. It does not infer positivity
from reality alone or assume each exterior root is real. This supplies
the exact assertion about Q in manuscript lines 169–174.

`vandermonde_conj_of_reverse` (lines 89–101) applies the map through the
determinant and permutes the Vandermonde's root rows. The helper's
conjugacy premise is genuine and is discharged for both actual lists.
`rootVandermondeProduct_conj` (lines 103–112) multiplies the two equal
reversal signs. Consequently `V(R)V(O)` is real, as claimed in manuscript
line 213. No assertion that either individual factor is real, positive,
or nonzero occurs. Those stronger assertions would in general be wrong
or would need the separate positive-theta distinctness hypotheses.

There is no added numerical computation beyond the two-element central
swap and sign cases, no custom axiom, no assumed normalizer identity,
and no principal-argument reduction. The code reuses permutation signs,
mapped determinants, finite product reindexing and the intermediate
value theorem from the pinned library.

## Actual local evidence, independently inspected

`evidence/logs/root-list-products-01.json` has SHA-256
`38a63efc00a5ce04d9a76e45b589b36eb73888a53b16268a41aec92b30cc79e9`.
It records `exit_code: 0`, `source_unchanged: true`, and the command
`lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/RootListProducts.olean MF21Restart/RootListProducts.lean`.
The reviewer independently recomputed and matched its source, log and
output hashes. The successful log has SHA-256
`05349e6b5325e3eb2bf90fc827c9662ceef83ab1b87d3df4a39f7408fd561873`;
the output has SHA-256
`e577183afc4c5987c98eeb9c4eac2843c604d45683a8159b5e396273162f21ee`.
All seven printed declarations list only `propext`, `Classical.choice`
and `Quot.sound`.

For `BoundaryConjugation`, the coordinator reported an actual serialized
02 run with exit zero. The reviewer observed
`evidence/logs/boundary-conjugation-02.log`, SHA-256
`dae5cff9f1772c3e1b76eb63adca1338ab0967da22207f649e41220ce17fdfeb`,
which contains four reports, each with only those same three axioms.
There is no per-test `boundary-conjugation-02.json` on disk at review time.
The current output hash is
`a27a44f2fd05d1cdb6f001c749a8e261cfef09f6cff64dcd28e68b93bf2e9073`;
without a recorded source/output manifest for that direct invocation,
the reviewer does not independently attribute this output to that run.
The source and statement hashes above freeze the exact reviewed text;
a later integrated source-matched run can strengthen this evidence.

## Remaining scope

These files do not prove the leading coefficient factorization, the
normalizer's nonvanishing or smooth quotient, the real normalized
determinant equation, the error estimates, root indexing, or the final
MF-21 theorem. They prove the conjugation and product facts needed by
those subsequent steps. No Comparator, Linux sandbox, or GitHub test is
claimed here. No material mathematical or statement-fidelity issue was
found in this scope.
