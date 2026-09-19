import NLA.MF14Degree44.ProductSpan
import NLA.MF14Degree44.DegenerationAtZero
import Mathlib.Tactic.Ring

/- Exact monic border path for Marcus Webb's degree44 proof. Formalization:
George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology; Codex assistance. All polynomial tails
are retained, including degrees13 through16 before the limit. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
namespace NLA.MF14Degree44

def borderPathD (xi : Fin 7 → ℂ) : ℂ := xi 5

def borderPathC (alpha : ℂ) (xi : Fin 7 → ℂ) : ℂ :=
  xi 4 - 2 * alpha * borderPathD xi

def borderPathB (alpha eta : ℂ) (xi : Fin 7 → ℂ) : ℂ :=
  xi 3 - 2 * alpha * borderPathC alpha xi - (alpha ^ 2 + 2 * eta) * borderPathD xi

def borderPathA (alpha eta : ℂ) (xi : Fin 7 → ℂ) : ℂ :=
  xi 2 - 2 * alpha * borderPathB alpha eta xi -
    (eta + alpha ^ 2) * borderPathC alpha xi - 2 * alpha * eta * borderPathD xi

def monicBorderPath (alpha eta gamma : ℂ) (xi : Fin 7 → ℂ) (s : ℂ) : Poly :=
  let a := borderPathA alpha eta xi
  let b := borderPathB alpha eta xi
  let c := borderPathC alpha xi
  let d := borderPathD xi
  let r := Rparam alpha eta gamma s
  let q := Q alpha
  degenerationZ alpha eta gamma s + C a * (X ^ 2 * r) + C b * q ^ 2 +
    C c * (q * r) + C d * r ^ 2 + C (xi 0) * X ^ 3 - C (a * eta) * X ^ 5 +
    C (xi 1 - a * alpha - b * alpha ^ 2 - c * alpha * eta - d * eta ^ 2) * X ^ 6

theorem monic_border_path_mem (alpha eta gamma : ℂ) (xi : Fin 7 → ℂ)
    (s : ℂ) (hs : s ≠ 0) : monicBorderPath alpha eta gamma xi s ∈ productSpan alpha eta gamma s := by
  let S := productSpan alpha eta gamma s
  have h7 := polynomial_C_mul_mem S (borderPathA alpha eta xi)
    (product_span_basis_mem alpha eta gamma s 9)
  have h8 := polynomial_C_mul_mem S (borderPathB alpha eta xi)
    (product_span_basis_mem alpha eta gamma s 7)
  have h9 := polynomial_C_mul_mem S (borderPathC alpha xi)
    (product_span_basis_mem alpha eta gamma s 10)
  have h10 := polynomial_C_mul_mem S (borderPathD xi)
    (product_span_basis_mem alpha eta gamma s 11)
  have h3 := polynomial_C_mul_mem S (xi 0) (product_span_monomial_mem alpha eta gamma s 3)
  have h5 := polynomial_C_mul_mem S (borderPathA alpha eta xi * eta)
    (product_span_monomial_mem alpha eta gamma s 5)
  have h6 := polynomial_C_mul_mem S
    (xi 1 - borderPathA alpha eta xi * alpha - borderPathB alpha eta xi * alpha ^ 2 -
      borderPathC alpha xi * alpha * eta - borderPathD xi * eta ^ 2)
    (product_span_monomial_mem alpha eta gamma s 6)
  exact S.add_mem (S.sub_mem
    (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem
      (degeneration_in_span alpha eta gamma s hs) h7) h8) h9) h10) h3) h5) h6

theorem monic_border_path_at_zero (alpha eta gamma : ℂ) (xi : Fin 7 → ℂ)
    (hgamma : 3 * alpha - 4 * gamma ^ 2 = xi 6) :
    monicBorderPath alpha eta gamma xi 0 = monicBorderPolynomial xi := by
  unfold monicBorderPath
  rw [degeneration_at_zero, hgamma]
  simp only [Rparam, Q, zero_pow (by decide : 2 ≠ 0), mul_zero, map_zero,
    zero_mul, zero_add, monicBorderPolynomial, borderPathA, borderPathB, borderPathC,
    borderPathD, map_sub, map_add, map_mul, map_pow, map_ofNat]
  ring

lemma moving_quad_at_zero_generic (alpha beta gamma : ℂ) (p : Poly) :
    movingQuad alpha (beta + alpha ^ 2) gamma 0 p =
      ![X ^ 2, Q alpha, R beta, p] := by
  have hR : Rparam alpha (beta + alpha ^ 2) gamma 0 - C alpha * Q alpha = R beta := by
    simp only [Rparam, Q, R, zero_pow (by decide : 2 ≠ 0), mul_zero, map_zero,
      zero_mul, zero_add, map_add, map_pow]
    ring
  change ![X ^ 2, Q alpha, Rparam alpha (beta + alpha ^ 2) gamma 0 - C alpha * Q alpha, p] = _
  rw [hR]

theorem moving_border_path_at_zero (alpha beta gamma : ℂ) (xi : Fin 7 → ℂ)
    (hgamma : 3 * alpha - 4 * gamma ^ 2 = xi 6) :
    movingQuad alpha (beta + alpha ^ 2) gamma 0
      (monicBorderPath alpha (beta + alpha ^ 2) gamma xi 0) = borderQuad alpha beta xi := by
  calc
    movingQuad alpha (beta + alpha ^ 2) gamma 0
        (monicBorderPath alpha (beta + alpha ^ 2) gamma xi 0) =
      movingQuad alpha (beta + alpha ^ 2) gamma 0 (monicBorderPolynomial xi) :=
        congrArg (movingQuad alpha (beta + alpha ^ 2) gamma 0)
          (monic_border_path_at_zero alpha (beta + alpha ^ 2) gamma xi hgamma)
    _ = borderQuad alpha beta xi := moving_quad_at_zero_generic alpha beta gamma _

#print axioms monic_border_path_mem
#assert_trust kernel monic_border_path_mem
#print axioms monic_border_path_at_zero
#assert_trust kernel monic_border_path_at_zero
#print axioms moving_border_path_at_zero
#assert_trust kernel moving_border_path_at_zero
end NLA.MF14Degree44
