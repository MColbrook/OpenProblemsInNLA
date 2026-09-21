import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Tactic

/-! The explicit quadratic-formula branch underlying manuscript Lemma 2.
The root-of-unity parameter substitution and smooth estimates come later. -/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

def stableQuadraticRoot (a : ℂ) : ℂ := (Complex.sqrt (1 + a ^ 2) - a) ^ 2

lemma complex_sqrt_sq (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  simpa only [Complex.sqrt, Nat.cast_ofNat] using
    Complex.cpow_nat_inv_pow z (by norm_num : (2 : ℕ) ≠ 0)

lemma sqrt_one_add_sq_re_pos (a : ℂ) (ha : 0 < a.re) :
    0 < (Complex.sqrt (1 + a ^ 2)).re := by
  let b := Complex.sqrt (1 + a ^ 2)
  have hb : b ^ 2 = 1 + a ^ 2 := complex_sqrt_sq _
  have hbnonneg : 0 ≤ b.re := by
    dsimp [b, Complex.sqrt]
    rw [Complex.cpow_inv_two_re]
    exact Real.sqrt_nonneg _
  have hbre := congrArg Complex.re hb
  have hbim := congrArg Complex.im hb
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.one_re, Complex.one_im, zero_add] at hbre hbim
  change 0 < b.re
  by_contra h
  have hbzero : b.re = 0 := le_antisymm (le_of_not_gt h) hbnonneg
  rw [hbzero, zero_mul, mul_zero, zero_add] at hbim
  have hprod : a.re * a.im = 0 := by nlinarith [hbim]
  have haim : a.im = 0 := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt ha)
  rw [hbzero, haim] at hbre
  nlinarith [sq_nonneg a.re, sq_nonneg b.im]

lemma sqrt_one_add_sq_factors (a : ℂ) :
    (Complex.sqrt (1 + a ^ 2) - a) * (Complex.sqrt (1 + a ^ 2) + a) = 1 := by
  have h := complex_sqrt_sq (1 + a ^ 2)
  linear_combination h

theorem stableQuadraticRoot_ne_zero (a : ℂ) : stableQuadraticRoot a ≠ 0 := by
  have h := sqrt_one_add_sq_factors a
  have hne : Complex.sqrt (1 + a ^ 2) - a ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at h
    exact zero_ne_one h
  exact pow_ne_zero _ hne

theorem stableQuadraticRoot_equation (a : ℂ) :
    2 - stableQuadraticRoot a - (stableQuadraticRoot a)⁻¹ = -4 * a ^ 2 := by
  let b := Complex.sqrt (1 + a ^ 2)
  have hprod : (b - a) * (b + a) = 1 := sqrt_one_add_sq_factors a
  have hne : b - a ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hprod
    exact zero_ne_one hprod
  have hinv : (b - a)⁻¹ = b + a := by
    apply mul_left_cancel₀ hne
    rw [mul_inv_cancel₀ hne, hprod]
  change 2 - (b - a) ^ 2 - ((b - a) ^ 2)⁻¹ = -4 * a ^ 2
  rw [← inv_pow, hinv]
  have hb : b ^ 2 = 1 + a ^ 2 := complex_sqrt_sq _
  linear_combination -2 * hb

theorem stableQuadraticRoot_norm_lt_one (a : ℂ) (ha : 0 < a.re) :
    ‖stableQuadraticRoot a‖ < 1 := by
  let b := Complex.sqrt (1 + a ^ 2)
  have hbpos : 0 < b.re := sqrt_one_add_sq_re_pos a ha
  have hb : b ^ 2 = 1 + a ^ 2 := complex_sqrt_sq _
  have him := congrArg Complex.im hb
  simp only [pow_two, Complex.mul_im, Complex.add_im, Complex.one_im, zero_add] at him
  have hproduct : b.re * (a.im * b.im) = a.re * a.im ^ 2 := by
    nlinarith [congrArg (fun x : ℝ => x * a.im) him]
  have himprod : 0 ≤ a.im * b.im := by
    have hnonneg : 0 ≤ b.re * (a.im * b.im) := by
      rw [hproduct]
      exact mul_nonneg ha.le (sq_nonneg _)
    exact nonneg_of_mul_nonneg_right hnonneg hbpos
  have hdot : 0 < (b * (starRingEnd ℂ) a).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    nlinarith [mul_pos hbpos ha]
  have hsq : ‖b - a‖ ^ 2 < ‖b + a‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub, Complex.normSq_add]
    linarith
  have hnormlt : ‖b - a‖ < ‖b + a‖ := by
    nlinarith [norm_nonneg (b - a), norm_nonneg (b + a)]
  have hprod : ‖b - a‖ * ‖b + a‖ = 1 := by
    have h := congrArg norm (sqrt_one_add_sq_factors a)
    simpa only [b, norm_mul, norm_one] using h
  have hsmall : ‖b - a‖ < 1 := by
    by_contra h
    have hge : 1 ≤ ‖b - a‖ := le_of_not_gt h
    have hlarge : 1 < ‖b + a‖ := lt_of_le_of_lt hge hnormlt
    have hle : ‖b + a‖ ≤ ‖b - a‖ * ‖b + a‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hge (norm_nonneg (b + a))
    linarith
  change ‖(b - a) ^ 2‖ < 1
  rw [norm_pow]
  nlinarith [norm_nonneg (b - a)]

theorem stableQuadraticRoot_zero : stableQuadraticRoot 0 = 1 := by
  simp [stableQuadraticRoot]

#print axioms stableQuadraticRoot_ne_zero
#print axioms stableQuadraticRoot_equation
#print axioms stableQuadraticRoot_norm_lt_one
#print axioms stableQuadraticRoot_zero

end MF21Restart
