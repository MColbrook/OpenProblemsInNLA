import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Data.Fin.VecNotation

/-!
Transparent draft definitions for the original MF-14 circuit/closure problem.
Mathematical solution: Marcus Webb, The University of Manchester.
Formalization in preparation: George Stepaniants, Department of Computing and
Mathematical Sciences, California Institute of Technology.

No mathematical proof is implemented here. The draft statement modules and
all later numerical definitions require two independent reviews before freeze.
-/

noncomputable section

open Set Polynomial

namespace NLA.MF14

abbrev Poly := Polynomial ℂ
abbrev CoefficientSpace := Fin 129 → ℂ
abbrev GatePolynomials := Fin 7 → Poly
abbrev Parameters := Fin 49 → ℂ

/-- Available polynomials before zero-based gate `k`: initial `1, X` and
the outputs of strictly earlier multiplication gates. -/
def availableGenerators (q : GatePolynomials) (k : ℕ) : Set Poly :=
  {1, X} ∪ {p | ∃ j : Fin 7, j.val < k ∧ p = q j}

def availableSpace (q : GatePolynomials) (k : ℕ) : Submodule ℂ Poly :=
  Submodule.span ℂ (availableGenerators q k)

/-- Seven chronological multiplication gates. Free complex linear
combinations are represented by membership in the available vector space. -/
def IsSevenGateCircuit (q : GatePolynomials) : Prop :=
  ∀ k : Fin 7, ∃ u v : Poly,
    u ∈ availableSpace q k.val ∧ v ∈ availableSpace q k.val ∧ q k = u * v

/-- A circuit using an arbitrary prefix of at most seven multiplication slots.
Only the first `m` outputs are constrained or available. Unused storage slots
have no mathematical effect; in particular `m = 0` permits every free linear
combination of `1` and `X`. -/
def IsAtMostSevenProductOutput (p : Poly) : Prop :=
  ∃ (m : ℕ) (q : GatePolynomials), m ≤ 7 ∧
    (∀ k : Fin 7, k.val < m → ∃ u v : Poly,
      u ∈ availableSpace q k.val ∧ v ∈ availableSpace q k.val ∧ q k = u * v) ∧
    p ∈ availableSpace q m

/-- Outputs after seven gates; circuits with fewer gates will be identified
with these by proving zero-gate padding, not by an assumed equivalence. -/
def IsSevenProductOutput (p : Poly) : Prop :=
  ∃ q : GatePolynomials, IsSevenGateCircuit q ∧ p ∈ availableSpace q 7

def coefficientVector (p : Poly) : CoefficientSpace :=
  fun i => p.coeff i.val

def outputVectors : Set CoefficientSpace :=
  coefficientVector '' {p | IsSevenProductOutput p}

/-- The exact canonical closure: simultaneous zero set of every complex
polynomial equation vanishing on the given set of full coefficient vectors. -/
def vanishingHull (S : Set CoefficientSpace) : Set CoefficientSpace :=
  {z | ∀ F : MvPolynomial (Fin 129) ℂ,
    (∀ w ∈ S, MvPolynomial.eval w F = 0) → MvPolynomial.eval z F = 0}

def sevenProductClosure : Set CoefficientSpace := vanishingHull outputVectors

/-- The full coefficient plane, including zero and all degrees below `d`. -/
def degreePlane (d : ℕ) : Set CoefficientSpace :=
  {z | ∀ i : Fin 129, d < i.val → z i = 0}

def CoversDegree (d : ℕ) : Prop := degreePlane d ⊆ sevenProductClosure

def coveredDegrees : Set ℕ := {d | d ≤ 128 ∧ CoversDegree d}

/-- The complete polynomial family, with all coefficients through degree 128.
The seed indexing agrees with the original 49-parameter source. -/
def familyBasis (θ : Parameters) : Fin 9 → Poly :=
  let q1 : Poly := X ^ 2
  let q2 : Poly := X ^ 4 + C (θ 0) * X ^ 3
  let q3 : Poly := q2 ^ 2 + C (θ 1) * X ^ 2 * q2 +
    C (θ 2) * X * q2 + C (θ 3) * X ^ 3
  let q4 : Poly :=
    (q3 + C (θ 4) * X + C (θ 5) * q1 + C (θ 6) * q2) *
    (q3 + C (θ 7) * X + C (θ 8) * q1 + C (θ 9) * q2)
  let q5 : Poly :=
    (q4 + C (θ 10) * X + C (θ 11) * q1 + C (θ 12) * q2 + C (θ 13) * q3) *
    (q4 + C (θ 14) * X + C (θ 15) * q1 + C (θ 16) * q2 + C (θ 17) * q3)
  let q6 : Poly :=
    (q5 + C (θ 18) * X + C (θ 19) * q1 + C (θ 20) * q2 + C (θ 21) * q3 +
      C (θ 22) * q4) *
    (q5 + C (θ 23) * X + C (θ 24) * q1 + C (θ 25) * q2 + C (θ 26) * q3 +
      C (θ 27) * q4)
  let q7 : Poly :=
    (q6 + C (θ 28) * X + C (θ 29) * q1 + C (θ 30) * q2 + C (θ 31) * q3 +
      C (θ 32) * q4 + C (θ 33) * q5) *
    (q6 + C (θ 34) * X + C (θ 35) * q1 + C (θ 36) * q2 + C (θ 37) * q3 +
      C (θ 38) * q4 + C (θ 39) * q5)
  ![1, X, q1, q2, q3, q4, q5, q6, q7]

def familyPolynomial (θ : Parameters) : Poly :=
  ∑ i : Fin 9, C (θ (Fin.natAdd 40 i)) * familyBasis θ i

/-- Full, untruncated coefficient map. -/
def familyVector (θ : Parameters) : CoefficientSpace :=
  coefficientVector (familyPolynomial θ)

/-- The nonempty generic gate degree profile used only in the normal-form
bridge. It is not a hypothesis of the final coverage theorem. -/
def HasDoublingDegrees (q : GatePolynomials) : Prop :=
  ∀ k : Fin 7, (q k).natDegree = 2 ^ (k.val + 1)

end NLA.MF14
