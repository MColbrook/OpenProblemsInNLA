# Independent determinant derivative review

Verdict: **APPROVE**, for the four exact public results in
`DeterminantMultiplicity.lean`. This is the general complex matrix-curve
ingredient in manuscript Lemma 4, not a proof of the required simple
spectral zeros or of the complete MF-21 target.

Reviewer: `/root/mf21_restart_lean_audit`, 20 September 2026. I did not
author or edit this source. I inspected its entire final proof, statement
lock, the manuscript, and the relevant pinned Mathlib definitions and
theorems. I ran no compiler. The pinned referee standard has SHA-256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Exact inspected artifacts

Paths are relative to `MF21-restart`.

| Path | SHA-256 |
| --- | --- |
| `MF21Restart/DeterminantMultiplicity.lean` | `fab853f9067b237317147e006d42860889ef6a819c0cd500ca5cf85ed59bf7cb` |
| `DETERMINANT_MULTIPLICITY_STATEMENTS.md` | `2c4a52cfe4bcba6c8d1d38aaebcd1e8a3ef785b3142e44dc99a929ba6eeaf213` |
| `original-proof/solution.md` | `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa` |
| `evidence/logs/determinant-multiplicity-03.log` | `433e0cade9faaa77d25bdd1342bcae5f25d22c961779590b5be9cecd469c3aa7` |
| `.lake/build/lib/lean/MF21Restart/DeterminantMultiplicity.olean` | `e7e810134de130d0446c033114807a6f0d8223dc0b53e417e8ddff15de86061e` |

The coordinator reports actual serialized local compilation 03 exited 0.
I independently rehashed the files above and inspected log 03, which
contains all four expected axiom reports and no error. Each report lists
exactly `propext`, `Classical.choice`, and `Quot.sound`. At review time,
there is no retained `determinant-multiplicity-03.json`; the only individual
JSON record found is compilation 01, which **failed** and refers to an
earlier source. Accordingly, the current output hash is recorded as an
inspected artifact, but is not claimed to have been independently matched
against a successful execution record. This documentation distinction
does not alter the static statement/proof verdict. It must be closed by a
source-matched successful record before publication. No GitHub Comparator
execution is claimed.

## Statement fidelity and nonvacuity

The first, third, and fourth theorems use
`Module.finrank ℂ (LinearMap.ker A.mulVecLin) >= 2`, with the matrix
acting on complex vectors. The scalar field is essential: for the curve
`diag(t,1)` at zero, real kernel dimension is two while the determinant
derivative is one. The source uses the correct complex dimension and
does not have that counterexample.

The hypotheses are naturally impossible for sizes zero and one; they
are realized for every size at least two by a zero matrix. They do not
assert determinant derivative zero, singularity of a replaced row,
adjugate vanishing, or any restatement of the desired conclusion. The
derivative formula theorem at lines 60–72 has no nullity assumption and
also behaves correctly at size zero: the empty determinant is constant
one and the empty derivative sum is zero.

The exact types at lines 26–30, 60–65, 75–80, and 88–93 match the four
locked statements. The manuscript uses this fact at
`solution.md:239`: nullity at least two of the boundary matrix forces
zero derivative of its determinant. This module proves that underlying
fact for an arbitrary differentiable complex matrix curve. It does not
smuggle in the equality of boundary and Toeplitz kernel dimensions or
the existence of a nonzero determinant derivative.

## Proof checks

At lines 31–41, the new row's complex-linear dot-product functional is
restricted to `ker A`. Its codomain has complex dimension one. Mathlib's
`LinearMap.ker_ne_bot_of_finrank_lt` therefore produces a nonzero vector
in the functional's kernel. As an element of `ker A`, it is also killed
by A. At lines 42–48, `Matrix.updateRow_mulVec` shows that the replaced
matrix kills this same vector; subtype extensionality correctly preserves
its nonzero status. The actual determinant/kernel equivalence then proves
the replacement determinant is zero. The row functional is bilinear dot
product, not a Hermitian inner product, as required for matrix action.

Lines 50–57 package the actual alternating row determinant as a complex
continuous multilinear map. Continuity comes from determinant continuity;
the value is definitionally `Matrix.det`. Lines 66–72 apply its proved
Mathlib Fréchet derivative, restrict the derivative to real scalars, and
compose with the real-parameter matrix curve. The linear derivative is
the sum of single-row replacements. Thus the formula has the correct
row orientation, no missing conjugations, and exactly one replacement
per summand. The `erw` and explicit `change` resolve the definitional
matrix representation; they do not change the function or derivative.

Lines 81–85 apply the first theorem to each row replacement and sum the
zeros. Lines 94–95 assemble the entrywise derivatives with two finite-Pi
derivative equivalences before applying the matrix-valued theorem.
Pointwise differentiability is sufficient; no global smoothness or
uniform derivative bound is presumed.

## Trust and remaining scope

The module imports only pinned Mathlib infrastructure. There is no
`sorry`, `admit`, custom axiom, unsafe shortcut, `native_decide`, Challenge
import, legacy formalization import, or numerical certificate. The four
local axiom reports agree with that source inspection. There is no
gratuitous computation or finite enumeration.

No correctness or source-fidelity change is requested. Converting a
simple boundary-determinant zero into a one-dimensional actual Toeplitz
eigenspace requires the separately proved boundary-kernel equivalence;
algebraic simplicity additionally requires the matrix's spectral
structure. Proving such simple zeros from the determinant asymptotics
is also outside this review. This helper does not increase the number
of completed original targets.
