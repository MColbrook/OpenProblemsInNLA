# Independent Vandermonde and normalized boundary coefficient review

Verdict: **APPROVE**, for the three public scaling results in
`VandermondeScale.lean` and ten public results in `NormalizedBoundary.lean`
at the exact hashes below. They prove an exact common vanishing factor
`theta^(m*(m-1))` for each surviving actual boundary coefficient, with
an analytic normalized factor nonzero at zero. They do not yet normalize
the full denominator or prove the coefficient bounds in manuscript (18).

Reviewer: `/root/mf21_restart_lean_audit`, 20 September 2026. I did not
author or edit either reviewed module. I independently read both complete
sources and locks, the existing boundary coefficient definitions and
factorization, the analytic slope proof, the manuscript, and the relevant
pinned Mathlib determinant and analytic APIs. I authored some imported
root infrastructure, including `CharacteristicRoots` and `RootTangents`;
this report **does not count as independent proof review of those
dependencies**. I checked their use here against their frozen statements.
The newly authored `RootDifferences` is also excluded from independent
scope and is not imported by either reviewed module. I ran no compiler.
The pinned referee standard has SHA-256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Exact reviewed sources

Paths are relative to `MF21-restart`.

| Path | SHA-256 |
| --- | --- |
| `MF21Restart/VandermondeScale.lean` | `28f94768350f6ee58f26bd25eba96528cf5cb041423d6085bdf6ba6058c19858` |
| `VANDERMONDE_SCALE_STATEMENTS.md` | `d59313808bda7c33aee05b226956a6a8924426f09ece644c4bf4cb79d366a563` |
| `MF21Restart/NormalizedBoundary.lean` | `3d45a02be0ce050f37be4ec3db227504028730c9283f4148d5739b37c48a9261` |
| `NORMALIZED_BOUNDARY_STATEMENTS.md` | `17bbca3cecdc1088d1dfa0f8d4bed5cde78d28d6bdd93c39b2961ba2b494fc28` |
| `MF21Restart/BoundaryExpansion.lean` | `bc873ac5a5cb569d3dda0bc3b6ecf623e09d326f0d82cd613fdc3149c24a3979` |
| `MF21Restart/RootTangents.lean` | `a37f2ec6cc1c1385b4219cb927e2164e0cfab3f584cd912ac48974391f7a299f` |
| `MF21Restart/ConcreteBoundary.lean` | `bde3c2195d13e981249f6eebf9691b05d1f186edad7aa7b9e72c133f911063f4` |
| `MF21Restart/AnalyticSlope.lean` | `134bef6e7863c9e9932fde4c220d31a2d019d48a5820bf72e398dc058a2a2dc7` |
| `original-proof/solution.md` | `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa` |

## Exact Vandermonde scaling

`VandermondeScale.lean:11–21` defines the exponent as the natural sum
`sum (i:Fin k), i.val`, and proves twice that exponent is `k*(k-1)`.
Induction adds the final index k when the size grows from k to k+1.
The separate zero/successor treatment handles natural subtraction
without silently replacing it by integer subtraction. There is no
division by two or rounding issue.

Lines 23–31 use the literal `Matrix.vandermonde`, whose entry `(i,j)`
is `u(i)^j`. Scaling u by c multiplies its j-th power column by `c^j`.
Mathlib's `Matrix.det_mul_row` has exactly the column-indexed factor
`v j` in its statement despite its name; that actual API was inspected.
The product of these scalar factors is `c^(sum j.val)`. The source does
not replace the determinant by an unproved surrogate product.

Lines 33–39 translate the nodes by one using the proved translation
invariance of a Vandermonde determinant, then apply scalar scaling.
The identity is valid also at c=0. For k=0 and k=1 the exponent is zero
and the determinant is one, including the totalized `0^0=1` case. For
k>=2 and c=0, both sides vanish. No nonzero-scalar or distinctness
assumption is needed or introduced.

## Actual root slopes and removable endpoint values

`NormalizedBoundary.lean:12–13` defines each slope from the actual root
coordinate using `dslope` at zero. Its value at zero is the actual
derivative, while away from zero it equals `(w_i(theta)-w_i(0))/theta`.
It is not a totalized quotient whose value at zero has been arbitrarily
set to zero.

Lines 15–22 derive real analyticity from the proved global root
regularity and `analyticAt_dslope_of_forall_analyticAt`. I inspected the
supporting `AnalyticSlope.lean`: at zero it obtains an analytic factor
from Mathlib's order-one Taylor factorization, differentiates the exact
identity to identify the factor's zero value, and proves that factor
equals the completed slope. Away from zero it uses ordinary analytic
inversion and local equality with the slope. There is no assumed
analytic extension in the current theorem's hypotheses.

At lines 24–27, the actual `HasDerivAt` theorem yields precisely the
ordered tangent value. At lines 29–35, the general slope identity and
the actual root value one give the exact equality
`w_i(theta)=1+(theta:ℂ)*slope_i(theta)` for **every real theta**, including
zero. The regularity statements require m>=2, while these algebraic
and endpoint identities need no such restriction. All analyticity is
with respect to the real parameter; no entire complex-parameter claim
is made.

## Sublist determinant and exact vanishing exponent

Lines 37–38 define the normalized sublist Vandermonde as the actual
determinant on the slope values. Regularity at lines 40–53 follows by
the proved Vandermonde product formula and finite products of differences
of analytic root slopes. The product uses j>i and the orientation
`slope_j-slope_i`, matching the determinant's convention.

Lines 55–64 substitute `1+theta*slope` and apply the exact scaling
identity. Lines 66–72 prove the normalized determinant's value at zero
is nonzero for an injective sublist: its nodes are the actual distinct
tangents composed with that injection. This proves a nonzero leading
factor instead of assuming a leading-order expansion. Empty and
singleton sublists are handled by the determinant identity and the
injectivity criterion. Repeated-index sublists remain regular but are
correctly excluded from the nonvanishing conclusion.

The definition at lines 74–78 uses the actual integer unit
`boundaryLaplaceSign`, the inherited-order complement, and the
inherited-order chosen subset. `hs : s.card=m` and the proved complement
cardinality give two lists of size m. Their order embeddings are actual
injective maps; no separate distinctness assumption is requested from
the caller.

Lines 80–91 start with the literal previously proved
`boundaryCoefficient_vandermonde`, not an assumed determinant expansion.
Each size-m determinant contributes `theta^vandermondeDegree m`.
The independent exponent identity at lines 86–88 combines the two
powers using `2*vandermondeDegree m=m*(m-1)`. The final multiplication
preserves the actual Laplace sign. This gives exponent 2 when m=2 and
6 when m=3, agreeing with the two Vandermonde pair counts. The local
exponent equality also avoids rewriting the unrelated dependent index
dimension `2*m`; it is a proof-elaboration correction, with no change
to the statement or mathematics.

Lines 93–107 prove analyticity of the normalized coefficient and its
nonzero value at zero. The sign is an integer unit, hence ±1 and
nonzero after casting to ℂ. The two sublists' tangent Vandermondes are
nonzero by their actual injectivity. Thus no cancellation or fortuitous
vanishing of the leading factor is possible for a cardinality-m subset.

## Source fidelity and limits of the normalized coefficient

The result matches the **numerator** vanishing assertion after equation
(18), `original-proof/solution.md:202–211`: the signed product of two
size-m Vandermonde determinants has the common factor
`theta^(m*(m-1))` and a smooth nonzero leading factor.

`normalizedBoundaryCoefficient` is the normalized raw Laplace
coefficient from (14). It is **not yet** the manuscript's full `a_S`,
whose denominator is `2i*sigma*V(R)*V(O)*Q*|f|^2`. The regularity and
matching zero order of that denominator, its nonvanishing at π, and
the resulting quotient/derivative bounds must still be proved. This
module makes none of them a premise and does not claim them as a result.
At π some numerator factors may vanish when both oscillatory roots
occur in the same sublist, so zero-endpoint nonvanishing must not be
silently promoted to nonvanishing on the entire closed interval.

The statements match both locks. There is no wrong root ordering,
hidden global root-distinctness hypothesis, strengthened spectral
target, impossible size premise, or assumed asymptotic expansion.
There is no `sorry`, `admit`, custom axiom, unsafe shortcut,
`native_decide`, Challenge import, or legacy import in either reviewed
source. The proof is symbolic; no numerical certification or brute-force
enumeration is used.

## Local evidence and verification boundaries

| Artifact | SHA-256 |
| --- | --- |
| `evidence/logs/vandermonde-scale-02.log` | `3856b5d3b46e1b49d5c1017d268375f64a1b557ce520760ea1ebedd0f89750c9` |
| `.lake/build/lib/lean/MF21Restart/VandermondeScale.olean` | `419bf371d6eb86ac97005db7df347f550de229e9153d05cd2e860ce7d52baa44` |
| `evidence/logs/normalized-boundary-02.json` | `371cb627da7bf6b514dcf27ea56201826aa6695375b141c283d3386e502a7543` |
| `evidence/logs/normalized-boundary-02.log` | `7fa34f937e9f92bca32b28b639e80a526291992382f4978442c139a333c1f412` |
| `.lake/build/lib/lean/MF21Restart/NormalizedBoundary.olean` | `1115b22811f5634894a6f539ea7af61656535440b4189bf623ab1629213c8794` |

The coordinator reports actual local VandermondeScale02 exit code 0.
I inspected its log: all three reports have exactly `propext`,
`Classical.choice`, and `Quot.sound`, with only a tactic-style warning.
No individual JSON run record is presently retained for that run.
The displayed source, log, and current output hashes are independently
inspected artifacts; a successful integrated source-matched execution
record is still needed to close their execution provenance.

NormalizedBoundary02 has a retained actual local execution record,
starting at epoch `1789936851.41585` and ending at `1789936864.362475`.
Its command is

```text
lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/NormalizedBoundary.olean MF21Restart/NormalizedBoundary.lean
```

It records exit code 0 and unchanged source. I independently rehashed
its source, log, and compiled output; all three match the recorded
hashes. All ten printed declarations have exactly the same three
standard axioms. The earlier failed compilation 01 is not counted as
successful evidence.

No correctness or source-fidelity change is requested. The approvals
are limited to the named ingredients and exact hashes. No GitHub
Comparator execution, complete MF-21 Target proof, or additional
completed original problem is claimed.
