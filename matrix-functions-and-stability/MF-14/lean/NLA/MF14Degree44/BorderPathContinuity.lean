import NLA.MF14Degree44.MonicBorderPath
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic.FunProp

/- Coefficientwise continuity for the full border path; no uniform limit or
truncation is assumed. Marcus Webb's construction. Formalization:
George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology; Codex assistance. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
namespace NLA.MF14Degree44

def CoefficientsContinuous {ν : Type*} [TopologicalSpace ν] (F : ν → Poly) : Prop :=
  ∀ k : ℕ, Continuous (fun s => (F s).coeff k)

lemma CoefficientsContinuous.const {ν : Type*} [TopologicalSpace ν] (p : Poly) :
    CoefficientsContinuous (fun _ : ν => p) := fun _ => continuous_const

lemma CoefficientsContinuous.C {ν : Type*} [TopologicalSpace ν] {f : ν → ℂ}
    (hf : Continuous f) : CoefficientsContinuous (fun s => Polynomial.C (f s)) := by
  intro k
  by_cases hk : k = 0
  · simpa only [coeff_C, if_pos hk] using hf
  · simp only [coeff_C, if_neg hk]
    exact continuous_const

lemma CoefficientsContinuous.add {ν : Type*} [TopologicalSpace ν] {F G : ν → Poly}
    (hF : CoefficientsContinuous F) (hG : CoefficientsContinuous G) :
    CoefficientsContinuous (fun s => F s + G s) := by
  intro k
  simp only [coeff_add]
  exact continuous_add.comp ((hF k).prodMk (hG k))

lemma CoefficientsContinuous.sub {ν : Type*} [TopologicalSpace ν] {F G : ν → Poly}
    (hF : CoefficientsContinuous F) (hG : CoefficientsContinuous G) :
    CoefficientsContinuous (fun s => F s - G s) := by
  intro k
  simp only [coeff_sub]
  exact continuous_sub.comp ((hF k).prodMk (hG k))

lemma CoefficientsContinuous.mul {ν : Type*} [TopologicalSpace ν] {F G : ν → Poly}
    (hF : CoefficientsContinuous F) (hG : CoefficientsContinuous G) :
    CoefficientsContinuous (fun s => F s * G s) := by
  intro k
  simp only [coeff_mul]
  exact continuous_finsetSum _ (fun ij _ => (hF ij.1).mul (hG ij.2))

lemma CoefficientsContinuous.pow {ν : Type*} [TopologicalSpace ν] {F : ν → Poly}
    (hF : CoefficientsContinuous F) (k : ℕ) : CoefficientsContinuous (fun s => F s ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using (CoefficientsContinuous.const (ν := ν) (1 : Poly))
  | succ k ih => simpa only [pow_succ] using ih.mul hF

lemma Rparam_coefficients_continuous (alpha eta gamma : ℂ) :
    CoefficientsContinuous (Rparam alpha eta gamma) := by
  have ha : Continuous (fun s : ℂ => s ^ 2) := continuous_id.pow 2
  have hb : Continuous (fun s : ℂ => gamma * s) := continuous_const.mul continuous_id
  exact ((((CoefficientsContinuous.C ha).mul (CoefficientsContinuous.const (Q alpha ^ 2))).add
    (((CoefficientsContinuous.C hb).mul (CoefficientsContinuous.const (X ^ 2))).mul
      (CoefficientsContinuous.const (Q alpha)))).add
    (CoefficientsContinuous.const (X * Q alpha))).add
      (CoefficientsContinuous.const (C eta * X ^ 3))

lemma degenerationZ_coefficients_continuous (alpha eta gamma : ℂ) :
    CoefficientsContinuous (degenerationZ alpha eta gamma) := by
  have hc : Continuous (borderC alpha eta gamma) := by unfold borderC; fun_prop
  have hd : Continuous (borderD alpha eta gamma) := by unfold borderD; fun_prop
  intro k
  simp only [degenerationZ, coeff_add, coeff_C_mul]
  fun_prop

lemma monic_border_path_coefficients_continuous (alpha eta gamma : ℂ) (xi : Fin 7 → ℂ) :
    CoefficientsContinuous (monicBorderPath alpha eta gamma xi) := by
  have hR := Rparam_coefficients_continuous alpha eta gamma
  have h7 := (CoefficientsContinuous.const (C (borderPathA alpha eta xi))).mul
    ((CoefficientsContinuous.const (X ^ 2)).mul hR)
  have h8 : CoefficientsContinuous
      (fun _ : ℂ => C (borderPathB alpha eta xi) * Q alpha ^ 2) := CoefficientsContinuous.const _
  have h9 := (CoefficientsContinuous.const (C (borderPathC alpha xi))).mul
    ((CoefficientsContinuous.const (Q alpha)).mul hR)
  have h10 := (CoefficientsContinuous.const (C (borderPathD xi))).mul (hR.pow 2)
  have h3 : CoefficientsContinuous (fun _ : ℂ => C (xi 0) * X ^ 3) := CoefficientsContinuous.const _
  have h5 : CoefficientsContinuous
      (fun _ : ℂ => C (borderPathA alpha eta xi * eta) * X ^ 5) := CoefficientsContinuous.const _
  have h6 : CoefficientsContinuous (fun _ : ℂ =>
      C (xi 1 - borderPathA alpha eta xi * alpha - borderPathB alpha eta xi * alpha ^ 2 -
        borderPathC alpha xi * alpha * eta - borderPathD xi * eta ^ 2) * X ^ 6) :=
    CoefficientsContinuous.const _
  exact (((((((degenerationZ_coefficients_continuous alpha eta gamma).add h7).add h8).add
    h9).add h10).add h3).sub h5).add h6

lemma moving_border_path_continuous (alpha eta gamma : ℂ) (xi : Fin 7 → ℂ) :
    Continuous (fun s => quadVector (movingQuad alpha eta gamma s
      (monicBorderPath alpha eta gamma xi s))) := by
  apply continuous_pi
  intro i
  rcases i with ⟨i, k⟩
  fin_cases i
  · exact continuous_const
  · exact continuous_const
  · exact ((Rparam_coefficients_continuous alpha eta gamma).sub
      (CoefficientsContinuous.const (C alpha * Q alpha))) k.val
  · exact monic_border_path_coefficients_continuous alpha eta gamma xi k.val

#print axioms CoefficientsContinuous.mul
#assert_trust kernel CoefficientsContinuous.mul
#print axioms degenerationZ_coefficients_continuous
#assert_trust kernel degenerationZ_coefficients_continuous
#print axioms monic_border_path_coefficients_continuous
#assert_trust kernel monic_border_path_coefficients_continuous
#print axioms moving_border_path_continuous
#assert_trust kernel moving_border_path_continuous
end NLA.MF14Degree44
