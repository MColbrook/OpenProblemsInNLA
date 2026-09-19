import NLA.MF14Degree44.Definitions

/-!
The exact 45-parameter continuation and the compact integer Jacobian table.
No large matrix certificate, rank assertion, or proof is encoded as input.
Mathematical construction: Marcus Webb, The University of Manchester.
Formalization preparation: George Stepaniants, Department of Computing and
Mathematical Sciences, California Institute of Technology; Codex assistance.
-/

noncomputable section
open Polynomial
open scoped BigOperators
namespace NLA.MF14Degree44

/-- A contiguous parameter block, with an explicit bound preventing wrapping. -/
def parameterIndex {m : ℕ} (start : ℕ) (h : start + m ≤ 45) (i : Fin m) : Fin 45 :=
  ⟨start + i.val, (Nat.add_lt_add_left i.isLt start).trans_le h⟩

def linearCombination {m : ℕ} (c : Fin m → ℂ) (v : Fin m → Poly) : Poly :=
  ∑ i : Fin m, C (c i) * v i

def continuationBasis (theta : Parameters) (v : Quad) : Fin 9 → Poly :=
  let q := v 1
  let r := v 2
  let p := v 3
  let l3 : Fin 3 → Poly := ![X, v 0, q]
  let l4 : Fin 4 → Poly := ![X, v 0, q, r]
  let l5 : Fin 5 → Poly := ![X, v 0, q, r, p]
  let f :=
    (p + linearCombination (fun i : Fin 4 => theta (parameterIndex 9 (by decide) i)) l4) *
    (r + linearCombination (fun i : Fin 3 => theta (parameterIndex 13 (by decide) i)) l3)
  let g :=
    (f + linearCombination (fun i : Fin 5 => theta (parameterIndex 16 (by decide) i)) l5) *
    (r + linearCombination (fun i : Fin 3 => theta (parameterIndex 21 (by decide) i)) l3)
  let l6 : Fin 6 → Poly := ![X, v 0, q, r, p, f]
  let h :=
    (g + linearCombination (fun i : Fin 6 => theta (parameterIndex 24 (by decide) i)) l6) *
    (g + linearCombination (fun i : Fin 6 => theta (parameterIndex 30 (by decide) i)) l6)
  ![1, X, v 0, q, r, p, f, g, h]

def continuationPolynomial (theta : Parameters) (v : Quad) : Poly :=
  linearCombination (fun i : Fin 9 => theta (parameterIndex 36 (by decide) i))
    (continuationBasis theta v)

def continuationMap (theta : Parameters) (z : QuadSpace) : NLA.MF14.CoefficientSpace :=
  NLA.MF14.coefficientVector (continuationPolynomial theta (decodeQuad z))

def familyQuad (theta : Parameters) : Quad :=
  borderQuad (theta 0) (theta 1)
    (fun i : Fin 7 => theta (parameterIndex 2 (by decide) i))

def familyPolynomial (theta : Parameters) : Poly :=
  continuationPolynomial theta (familyQuad theta)

def coefficientMap (theta : Parameters) : Fin 45 → ℂ :=
  fun i => (familyPolynomial theta).coeff i.val

def fullFamilyVector (theta : Parameters) : NLA.MF14.CoefficientSpace :=
  NLA.MF14.coefficientVector (familyPolynomial theta)

/-- The full 129-vector of a degree-at-most-44 coefficient vector. -/
def embed44 (v : Fin 45 → ℂ) : NLA.MF14.CoefficientSpace :=
  fun i => if hi : i.val < 45 then v ⟨i.val, hi⟩ else 0

/-- alpha=b2=d3=d5=d6=z8=1; every other parameter is exactly zero. -/
def basePoint : Parameters :=
  fun i => if i = 0 ∨ i = 22 ∨ i = 32 ∨ i = 34 ∨ i = 35 ∨ i = 44 then 1 else 0

/-- Manuscript derivative columns over integers. Equality with the actual
complex derivative is an independent obligation, not part of this definition. -/
def integerDerivativeColumns : Fin 45 → Polynomial ℤ :=
  let q : Polynomial ℤ := X ^ 4 + X ^ 3
  let r : Polynomial ℤ := X ^ 5
  let p : Polynomial ℤ := X ^ 12
  let f : Polynomial ℤ := X ^ 17
  let g : Polynomial ℤ := X ^ 22 + X ^ 19
  let h := g * (g + q + p + f)
  let b := r + X ^ 2
  let k := 2 * g + q + p + f
  let l := k * b + g
  let lr := l * r
  let lp := l * p
  let kb := k * b
  let kf := k * f
  let gqpf := g + q + p + f
  ![g * X ^ 3,
    (lp + kf) * X ^ 3,
    (lr + g) * X ^ 3, (lr + g) * X ^ 6, (lr + g) * X ^ 7,
    (lr + g) * X ^ 8, (lr + g) * X ^ 9, (lr + g) * X ^ 10, (lr + g) * X ^ 11,
    lr * X, lr * X ^ 2, lr * q, lr * r,
    lp * X, lp * X ^ 2, lp * q,
    kb * X, kb * X ^ 2, kb * q, kb * r, kb * p,
    kf * X, kf * X ^ 2, kf * q,
    gqpf * X, gqpf * X ^ 2, gqpf * q, gqpf * r, gqpf * p, gqpf * f,
    g * X, g * X ^ 2, g * q, g * r, g * p, g * f,
    1, X, X ^ 2, q, r, p, f, g, h]

def integerJacobian : Matrix (Fin 45) (Fin 45) ℤ :=
  fun i j => (integerDerivativeColumns j).coeff i.val

def integerJacobianMod3 : Matrix (Fin 45) (Fin 45) (ZMod 3) :=
  fun i j => (integerJacobian i j : ZMod 3)

end NLA.MF14Degree44
