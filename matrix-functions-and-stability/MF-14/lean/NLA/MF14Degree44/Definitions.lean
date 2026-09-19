import NLA.MF14.Definitions
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.ZMod.Basic

/-!
Transparent proposed definitions for the degree-44 negative answer to MF-14.
The original NLA.MF14 circuit/closure/degree-plane definitions are imported
unchanged. This file does not replace the separate degree-47 statement gate.
No rank, density, limit, or coverage certificate is assumed in a data field.
Mathematical construction: Marcus Webb, The University of Manchester.
Earlier degree-42 result: Matthew J. Colbrook, University of Cambridge.
Formalization preparation: George Stepaniants, Department of Computing and
Mathematical Sciences, California Institute of Technology; Codex assistance.
-/

noncomputable section
open Polynomial
open scoped BigOperators

namespace NLA.MF14Degree44

abbrev Poly := NLA.MF14.Poly
abbrev Quad := Fin 4 → Poly
abbrev QuadIndex := Fin 4 × Fin 17
abbrev QuadSpace := QuadIndex → ℂ
abbrev Parameters := Fin 45 → ℂ

def IsCircuitPrefix (q : NLA.MF14.GatePolynomials) (m : ℕ) : Prop :=
  m ≤ 7 ∧ ∀ k : Fin 7, k.val < m → ∃ u v : Poly,
    u ∈ NLA.MF14.availableSpace q k.val ∧
    v ∈ NLA.MF14.availableSpace q k.val ∧ q k = u * v

/-- All entries use one common circuit prefix, not separate circuits. -/
def SimultaneouslyAvailable {r : ℕ} (m : ℕ) (v : Fin r → Poly) : Prop :=
  ∃ q : NLA.MF14.GatePolynomials, IsCircuitPrefix q m ∧
    ∀ i : Fin r, v i ∈ NLA.MF14.availableSpace q m

def JointFourAvailable (v : Quad) : Prop := SimultaneouslyAvailable 4 v

/-- Four products have degree at most 16; that fact is a separate obligation. -/
def quadVector (v : Quad) : QuadSpace := fun i => (v i.1).coeff i.2.val

def decodeQuad (z : QuadSpace) : Quad :=
  fun i => ∑ k : Fin 17, C (z (i, k)) * X ^ k.val

def jointFourVectors : Set QuadSpace := quadVector '' {v | JointFourAvailable v}

/-- Literal polynomial-equation closure in all four degree-16 coefficient spaces. -/
def jointFourClosure : Set QuadSpace :=
  {z | ∀ F : MvPolynomial QuadIndex ℂ,
    (∀ w ∈ jointFourVectors, MvPolynomial.eval w F = 0) →
      MvPolynomial.eval z F = 0}

def polynomiallyDenseRange {n : ℕ} (f : (Fin n → ℂ) → (Fin n → ℂ)) : Prop :=
  ∀ P : MvPolynomial (Fin n) ℂ,
    (∀ t : Fin n → ℂ, MvPolynomial.eval (f t) P = 0) → P = 0

attribute [-instance] InnerProductSpace.toNormedSpace in
def jacobianAt {n : ℕ} (f : (Fin n → ℂ) → (Fin n → ℂ))
    (a : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (fderiv ℂ f a) (Pi.single j 1) i

def Q (alpha : ℂ) : Poly := X ^ 4 + C alpha * X ^ 3

def R (beta : ℂ) : Poly := X ^ 5 + C beta * X ^ 3

def Rparam (alpha eta gamma s : ℂ) : Poly :=
  C (s ^ 2) * Q alpha ^ 2 + C (gamma * s) * X ^ 2 * Q alpha +
    X * Q alpha + C eta * X ^ 3

def thirdTuple (alpha eta gamma s : ℂ) : Fin 3 → Poly :=
  ![X ^ 2, Q alpha, Rparam alpha eta gamma s]

def productSpanBasis (alpha eta gamma s : ℂ) : Fin 12 → Poly :=
  let q := Q alpha
  let r := Rparam alpha eta gamma s
  ![1, X, X ^ 2, X ^ 3, X ^ 4, X ^ 5, X ^ 6,
    q ^ 2, X * r, X ^ 2 * r, q * r, r ^ 2]

def productSpan (alpha eta gamma s : ℂ) : Submodule ℂ Poly :=
  Submodule.span ℂ (Set.range (productSpanBasis alpha eta gamma s))

def fourthRows : Fin 12 → Fin 17 := ![0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16]

/-- Analysis coordinates on productSpan, not a permitted circuit operation. -/
def fourthCoordinates (p : Poly) : Fin 12 → ℂ :=
  fun i => p.coeff (fourthRows i).val

/-- Twelve actual affine input directions of one fourth product plus a free sum. -/
def fourthPolynomial (alpha eta gamma s lam : ℂ) (t : Fin 12 → ℂ) : Poly :=
  let q := Q alpha
  let r := Rparam alpha eta gamma s
  let u := r + C (t 5) * X + C (t 6) * X ^ 2 + C (t 7) * q
  let v := q + C lam * X ^ 2 + C (t 8) * X + C (t 9) * X ^ 2 +
    C (t 10) * q + C (t 11) * r
  let w := C (t 0) + C (t 1) * X + C (t 2) * X ^ 2 +
    C (t 3) * q + C (t 4) * r
  u * v + w

def fourthCoefficientMap (alpha eta gamma s lam : ℂ) (t : Fin 12 → ℂ) : Fin 12 → ℂ :=
  fourthCoordinates (fourthPolynomial alpha eta gamma s lam t)

def fourthDerivativeColumns (alpha eta gamma s lam : ℂ) : Fin 12 → Poly :=
  let q := Q alpha
  let r := Rparam alpha eta gamma s
  let v := q + C lam * X ^ 2
  ![1, X, X ^ 2, q, r, X * v, X ^ 2 * v, q * v,
    X * r, X ^ 2 * r, q * r, r ^ 2]

def fourthJacobian (alpha eta gamma s lam : ℂ) : Matrix (Fin 12) (Fin 12) ℂ :=
  fun i j => (fourthDerivativeColumns alpha eta gamma s lam j).coeff (fourthRows i).val

def fourthMinor (alpha eta gamma s lam : ℂ) : ℂ :=
  (s ^ 2) ^ 5 * (lam - eta - alpha * lam * (gamma * s - s ^ 2 * lam))

def GoodBorderParameter (alpha eta gamma s : ℂ) : Prop :=
  s ≠ 0 ∧ gamma * s - 2 * s ^ 2 ≠ 0 ∧
    fourthMinor alpha eta gamma s (eta + 1) ≠ 0

def movingQuad (alpha eta gamma s : ℂ) (p : Poly) : Quad :=
  ![X ^ 2, Q alpha, Rparam alpha eta gamma s - C alpha * Q alpha, p]

def monicBorderPolynomial (xi : Fin 7 → ℂ) : Poly :=
  X ^ 12 + C (xi 0) * X ^ 3 + C (xi 1) * X ^ 6 + C (xi 2) * X ^ 7 +
    C (xi 3) * X ^ 8 + C (xi 4) * X ^ 9 + C (xi 5) * X ^ 10 + C (xi 6) * X ^ 11

def borderQuad (alpha beta : ℂ) (xi : Fin 7 → ℂ) : Quad :=
  ![X ^ 2, Q alpha, R beta, monicBorderPolynomial xi]

end NLA.MF14Degree44
