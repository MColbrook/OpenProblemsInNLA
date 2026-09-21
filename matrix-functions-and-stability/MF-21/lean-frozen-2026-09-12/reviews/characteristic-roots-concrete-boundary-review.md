# Independent review: characteristic roots and the concrete boundary determinant

Verdict: **APPROVE** for the eight printed results in
`MF21Restart/CharacteristicRoots.lean` and `MF21Restart/ConcreteBoundary.lean`
at the source hashes below. I found no material correctness, source-fidelity,
or hypothesis-strengthening issue. This is the actual root-list construction
and the unnormalized equation (13) criterion, not determinant normalization,
an error estimate, or a completed MF-21 target.

I read both sources and their statement locks, the unchanged manuscript at
lines 142–159, the concrete boundary matrix, and the actual root, recurrence,
and eigenvalue bridges imported here. The review applies the pinned referee
rubric, SHA256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.
I edited no reviewed source and ran no compiler. My earlier authored
`RootParameters` is an explicitly identified dependency, not a new independent
approval of that source.

## Literal ordering, ranges, and distinctness

`CharacteristicRoots.characteristicRoots` (lines 19–27) uses precisely
the manuscript order `r_1,...,r_(m-1),z,z⁻¹,r_1⁻¹,...,r_(m-1)⁻¹`.
With zero-based `i : Fin (2*m)`, the stable branch `i<m-1` uses ell=i+1;
the two unit branches are i=m-1 and i=m; the last branch uses ell=i-m.
For the last branch, its negated preceding tests together with `i<2*m`
prove `1≤ell<m`. The natural subtractions do not silently truncate a
published positive index. The m≥2 premise is weaker than the manuscript's
m≥3 domain. Some statements could cover m=1 as well, but that is optional
generality, not a missing case of this task.

`characteristicRoots_ne_zero` (lines 78–86) is unconditional in the total
definition and proves nonvanishing from the actual exponential and quadratic
curve, using nonvanishing again before inversion. `characteristicRoots_norm_regions`
(lines 103–125) obtains strict norm below one for the stable branch and strict
norm above one for the reciprocal branch. The latter uses both nonzero norm
and the strict upper bound, not a reversed inverse inequality. The two central
branches have norm exactly one. These regions include theta=π but exclude
theta=0, where the strict inequalities would fail.

`characteristicRoots_injective` (lines 127–184) first uses those norm regions
to prevent collisions between the three groups. Within the stable group it
uses the proved injectivity of the actual stable root curves, with valid
indices in `1..m-1`. In the exterior group it cancels inversion and uses the
same theorem. Among the two unit positions, equality would force
`sin(theta)=-sin(theta)`, contradicting strict positivity on `(0,π)`.
Thus both endpoints are excluded exactly where necessary: all roots coalesce
at zero, and z=z⁻¹=-1 at π. No pairwise root separation premise is inserted
into the public statement.

## Exact spectral equation

`oscillatoryRoot_equation` (lines 49–55) proves
`2-z-z⁻¹ = 2-2*cos(theta)` for the literal complex exponential. The stable
branch helper (lines 191–196) uses the actual quadratic-root equation and
`omega^m=1`, then identifies `(2-2*cos(theta))^m` with the unchanged symbol
`(2*sin(theta/2))^(2*m)`. The inverse expression is unchanged under w↦w⁻¹,
as proved at lines 186–189. These facts cover all four branches in
`characteristicRoots_equation` (lines 203–214).

The equation is valid for every real theta, so its lack of an interval premise
is legitimate; only nonvanishing and distinctness for the basis application
need the separate proved facts. The 2m concrete, distinct roots provide the
root data required by the existing recurrence-basis proof. The present module
does not replace that basis argument with an assumed polynomial splitting or
an assumed complete root list.

## Actual determinant and eigenspace

`ConcreteBoundary.manuscriptBoundaryDeterminant` (lines 10–11) is exactly the
determinant of the existing `boundaryMatrix` at this concrete ordered list.
For row s<m its entries are w^s. For row s=m+k its entries are
w^(n+s)=w^(n+m+k), exactly the bottom block in manuscript (13). No scaling,
permutation, root-dependent quotient, or normalizing factor is hidden in
this definition.

`eigenvalue_iff_manuscriptBoundaryDeterminant_zero` (lines 13–20) applies
the proved real-to-complex eigenvalue/boundary criterion and discharges all
of its root hypotheses with the concrete theorems above. Its left side uses
the actual sorted-list accessor with bounds `1≤j≤n`, including j=n and
excluding all totalized out-of-range values. The conclusion is a two-way
existence equivalence; it does not yet identify an ordered phase index.

`manuscript_boundary_kernel_finrank_eq_eigenspace` (lines 22–30) similarly
specializes the already constructed complex-linear bijection between the
boundary kernel and actual Toeplitz eigenspace. It is equality of dimensions
over ℂ, not real dimension or only equivalence of nontriviality. No dimension
matching, determinant simplicity, or spectral multiplicity is assumed.
The theorem covers n=0: the interior eigenspace is zero and the distinct-root
boundary matrix is Vandermonde. No artificial n>0 premise removes that case.

## Smoothness and the artificial endpoint zero

`characteristicRoots_contDiff` (lines 32–45) proves each actual coordinate is
smooth on the whole real line. Its branch tests depend only on the fixed
index, so there is no parameter-dependent piecewise boundary to check. Stable
coordinates use Re κ>0 and the already proved smooth square-root branch;
reciprocals use actual global nonvanishing. The exponential branches are
smooth and nonzero. This theorem supplies root-coordinate smoothness; forming
the full matrix curve and determinant derivative is a further straightforward
composition, not claimed as an additional printed result here.

`manuscriptBoundaryDeterminant_pi` (lines 47–62) chooses the distinct column
indices m-1 and m and proves that their root values are both -1. Every power
in the two columns is consequently equal, so the determinant is zero. This
is the manuscript's artificial endpoint determinant zero. It is not presented
as an eigenvalue: the criterion above expressly requires theta<π. For n=0
the same endpoint vanishing remains true and is likewise compatible with
the absence of any spectral index. No normalized remainder E_n or its
endpoint value is defined or asserted by this module.

## Scope and trust

The statements match the two locks and the unchanged manuscript root list
and boundary criterion. Their only parameter restrictions are the declared
m≥2 and the necessary open interval for full root distinctness. No custom
axiom, `sorry`, `admit`, unsafe shortcut, `native_decide`, or numerical oracle
appears in the reviewed sources. Their symbolic finite case splits avoid
unnecessary numerical computation.

Still separate are the leading determinant terms and their nonvanishing
normalizer, the real remainder and its uniform derivative bound, the final
interval estimate, ordered phase-root counting, and the asymptotic expansion
construction. Neither module proves the full original target or increases
the completed-problem count. The standalone multiplicity bridge currently
being developed is also outside this independent review.

## Observed local evidence

The coordinator confirmed the actual serialized CharacteristicRoots01 run
returned exit 0 at the exact current source hash below. I read its log: all
four printed declarations report only `[propext, Classical.choice, Quot.sound]`.
There is no per-run JSON for that test in the inspected evidence directory;
no such record is claimed. Its exit-status/source-match attribution comes
from the coordinator, separately from the log I read.

The coordinator reported the actual ConcreteBoundary01 run succeeded. Its
observed JSON records exit 0, source unchanged, the source hash below, and
the exact command `lake env lean -j1 -M4096 -o
.lake/build/lib/lean/MF21Restart/ConcreteBoundary.olean
MF21Restart/ConcreteBoundary.lean` with `LEAN_NUM_THREADS=1`. The observed
log has the four standard-only axiom reports and matches the recorded hash.
The JSON explicitly records `comparator: not_run`. I ran no local test,
GitHub workflow, or Comparator, and this mathematical approval is not a
substitute for any of those checks.

| File | SHA256 |
|---|---|
| `MF21Restart/CharacteristicRoots.lean` | `d955e1ff32b205f3422e6c2161bf415a84cd733ccb1bb8e248a7dc4d2d7065e9` |
| `CHARACTERISTIC_ROOTS_STATEMENTS.md` | `cb2ed27b3eb10713e0899e5ba691c3cd98b4522e976038767255bd8430128b6e` |
| `MF21Restart/ConcreteBoundary.lean` | `bde3c2195d13e981249f6eebf9691b05d1f186edad7aa7b9e72c133f911063f4` |
| `CONCRETE_BOUNDARY_STATEMENTS.md` | `2c96af30d43760cf9f362da356f60555a95e06090614dfc4ec48d07908c03ab9` |
| `MF21Restart/StableRootSymmetry.lean` | `079597268e849c9fbca2adc00d049fce7dd38138278c685b051f5bc7c05700dd` |
| `MF21Restart/StableRootSmooth.lean` | `241296dc3b8ac1ca554a1685162f9952d7e4825d170abf56cba8d54f233f4011` |
| `MF21Restart/RootParameters.lean` | `c784f609c8eeba69db1ec5e7d3ca52ba0611777d662556c8fd8b6321b60af1fa` |
| `MF21Restart/RootDistinctness.lean` | `1a97a915d9b4058e84e48a564d4f5abddb24a2a68e54e655ca2f97028edbfce5` |
| `MF21Restart/RealComplexEigenvalue.lean` | `86f2f2cb01dea730e5c6c2042fa52652c25f0d99a683c6ffaef12bb404c8f2a0` |
| `MF21Restart/BoundaryMultiplicity.lean` | `94d136b3310fe28699fa3a386143e2b22d20f23f226541aecc49468492d659b9` |
| `MF21Restart/BoundaryExpansion.lean` | `bc873ac5a5cb569d3dda0bc3b6ecf623e09d326f0d82cd613fdc3149c24a3979` |
| `evidence/logs/characteristic-roots-01.log` | `17ed0e2c641ef59aeb0b06763d17db7b50a78a0137d35cba64b11361986438ef` |
| `evidence/logs/concrete-boundary-01.log` | `28dbcf8967b29a5071c120c23f75664c74a7cd73b50bf5eb8328c9bbb4ee3ea5` |
| `evidence/logs/concrete-boundary-01.json` | `6328edc1f88f0ed27e77ff2b1e5e03e4abab49500dd7b7c8d20b328137c96985` |
