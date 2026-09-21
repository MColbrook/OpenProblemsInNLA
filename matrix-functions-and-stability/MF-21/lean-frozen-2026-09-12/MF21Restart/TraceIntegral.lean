import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
The concrete diagonal integral in manuscript (28)–(29).

The statements were locked in TRACE_STATEMENTS.md before this proof was written.
The Beta/Gamma identity is specialized from Mathlib; no trace limit or integral
evaluation is assumed. This module does not establish the inverse-kernel limit
or identify finite Toeplitz traces with this integral.
-/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

/-- The natural polynomial case of Mathlib's proved Beta/Gamma identity. -/
theorem integral_pow_mul_one_sub_pow (p q : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ p * (1 - x) ^ q) =
      (p.factorial : ℝ) * (q.factorial : ℝ) /
        ((p + q + 1).factorial : ℝ) := by
  have hp : 0 < ((p : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
    positivity
  have hq : 0 < ((q : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
    positivity
  have hsum : (p : ℂ) + 1 + ((q : ℂ) + 1) =
      ((p + q + 1 : ℕ) : ℂ) + 1 := by
    push_cast <;> ring
  have hbeta : Complex.betaIntegral ((p : ℂ) + 1) ((q : ℂ) + 1) =
      (((∫ x in (0 : ℝ)..1, x ^ p * (1 - x) ^ q) : ℝ) : ℂ) := by
    unfold Complex.betaIntegral
    simp only [add_sub_cancel_right, Complex.cpow_natCast]
    have heq :
        (fun x : ℝ => (x : ℂ) ^ p * (1 - (x : ℂ)) ^ q) =
        (fun x : ℝ => ((x ^ p * (1 - x) ^ q : ℝ) : ℂ)) := by
      funext x
      simp only [Complex.ofReal_mul, Complex.ofReal_pow,
        Complex.ofReal_sub, Complex.ofReal_one]
    rw [heq, intervalIntegral.integral_ofReal]
  have hGamma := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := (p : ℂ) + 1) (t := (q : ℂ) + 1) hp hq
  rw [hsum, Complex.Gamma_nat_eq_factorial p, Complex.Gamma_nat_eq_factorial q,
    Complex.Gamma_nat_eq_factorial (p + q + 1), hbeta] at hGamma
  have hreal : (p.factorial : ℝ) * (q.factorial : ℝ) =
      ((p + q + 1).factorial : ℝ) *
        (∫ x in (0 : ℝ)..1, x ^ p * (1 - x) ^ q) := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_mul, Complex.ofReal_natCast] using hGamma
  have hfac : ((p + q + 1).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  apply (eq_div_iff hfac).2
  simpa only [mul_comm] using hreal.symm

/-- Integrating the diagonal polynomial (28) gives the exact value in (29). -/
theorem diagonal_kernel_integral_value (m : ℕ) (hm : 1 ≤ m) :
    (∫ x in (0 : ℝ)..1,
      x ^ (2 * m - 1) * (1 - x) ^ (2 * m - 1) /
        (((2 * m - 1 : ℕ) : ℝ) * ((m - 1).factorial : ℝ) ^ 2)) =
    ((2 * m - 1).factorial : ℝ) ^ 2 /
      (((4 * m - 1).factorial : ℝ) *
        ((2 * m - 1 : ℕ) : ℝ) * ((m - 1).factorial : ℝ) ^ 2) := by
  have hindex : (2 * m - 1) + (2 * m - 1) + 1 = 4 * m - 1 := by omega
  rw [intervalIntegral.integral_div, integral_pow_mul_one_sub_pow, hindex, div_div]
  simp only [pow_two, mul_assoc]

/-- The exact trace-integral constant is strictly positive, also for m=1. -/
theorem diagonal_kernel_integral_pos (m : ℕ) (hm : 1 ≤ m) :
    0 < (∫ x in (0 : ℝ)..1,
      x ^ (2 * m - 1) * (1 - x) ^ (2 * m - 1) /
        (((2 * m - 1 : ℕ) : ℝ) * ((m - 1).factorial : ℝ) ^ 2)) := by
  rw [diagonal_kernel_integral_value m hm]
  have ha : (0 : ℝ) < ((2 * m - 1).factorial : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hb : (0 : ℝ) < ((4 * m - 1).factorial : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hc : (0 : ℝ) < ((2 * m - 1 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (by omega)
  have hd : (0 : ℝ) < ((m - 1).factorial : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  exact div_pos (pow_pos ha 2) (mul_pos (mul_pos hb hc) (pow_pos hd 2))

/-- The trace-integral value is the real image of its explicit rational quotient. -/
theorem diagonal_kernel_integral_rational (m : ℕ) (hm : 1 ≤ m) :
    ∃ q : ℚ, (∫ x in (0 : ℝ)..1,
      x ^ (2 * m - 1) * (1 - x) ^ (2 * m - 1) /
        (((2 * m - 1 : ℕ) : ℝ) * ((m - 1).factorial : ℝ) ^ 2)) = (q : ℝ) := by
  refine ⟨((2 * m - 1).factorial : ℚ) ^ 2 /
    (((4 * m - 1).factorial : ℚ) *
      ((2 * m - 1 : ℕ) : ℚ) * ((m - 1).factorial : ℚ) ^ 2), ?_⟩
  rw [diagonal_kernel_integral_value m hm]
  simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_mul, Rat.cast_natCast]

#print axioms integral_pow_mul_one_sub_pow
#print axioms diagonal_kernel_integral_value
#print axioms diagonal_kernel_integral_pos
#print axioms diagonal_kernel_integral_rational

end MF21Restart
