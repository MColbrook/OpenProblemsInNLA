import MF21.MF21TraceSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.RingTheory.Polynomial.Pochhammer

/-! Exact integral constant in the direct discrete trace proof. -/
noncomputable section
open scoped BigOperators
open Finset Complex Polynomial
namespace MF21DiscreteLimits

/-- The polynomial beta integral, for all nonnegative integer exponents. -/
theorem integral_pow_one_sub_pow (a b : ℕ) :
    (∫ x in (0 : ℝ)..1, x^a * (1-x)^b) =
      (a.factorial : ℝ) * b.factorial / (a+b+1).factorial := by
  have hb := Complex.betaIntegral_eval_nat_add_one_right
    (u := (a : ℂ)+1) (by simp; positivity) b
  have hi : Complex.betaIntegral ((a : ℂ)+1) ((b : ℂ)+1) =
      Complex.ofReal (∫ x in (0 : ℝ)..1, x^a * (1-x)^b) := by
    unfold Complex.betaIntegral
    simp only [add_sub_cancel_right, Complex.cpow_natCast]
    rw [← intervalIntegral.integral_ofReal]
    congr 1
    ext x
    push_cast
    rfl
  rw [hi] at hb
  have hprod : (∏ j ∈ range (b+1), ((a : ℂ)+1+j)) =
      ((a+1).ascFactorial (b+1) : ℂ) := by
    rw [Nat.ascFactorial_eq_prod_range]
    push_cast
    rfl
  rw [hprod] at hb
  have hf : (a.factorial : ℂ) * ((a+1).ascFactorial (b+1) : ℂ) =
      ((a+b+1).factorial : ℂ) := by
    exact_mod_cast Nat.factorial_mul_ascFactorial a (b+1)
  have ha : (a.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  have hd : ((a+1).ascFactorial (b+1) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.ascFactorial_pos a (b+1))
  apply Complex.ofReal_injective
  rw [hb]
  push_cast
  rw [← hf]
  field_simp


/-- The constant furnished by the squared first inverse column agrees exactly
with the rational Green-kernel trace constant in the manuscript. -/
theorem first_column_integral_constant (r : ℕ) :
    ((∫ x in (0 : ℝ)..1, (x^r * (1-x)^(r+1))^2) /
      (r.factorial : ℝ)^2) / (2*r+2 : ℝ) =
        (MF21Audit.kernelTraceConstant (r+1) : ℝ) := by
  have he (x : ℝ) : (x^r * (1-x)^(r+1))^2 = x^(2*r) * (1-x)^(2*r+2) := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
    congr 1 <;> congr 1 <;> omega
  simp_rw [he]
  rw [integral_pow_one_sub_pow]
  unfold MF21Audit.kernelTraceConstant
  have h1 : 2*(r+1)-1 = 2*r+1 := by omega
  have h2 : 4*(r+1)-1 = 4*r+3 := by omega
  have h3 : r+1-1 = r := by omega
  rw [h1,h2,h3]
  push_cast
  rw [show 2*r+(2*r+2)+1 = 4*r+3 by omega,
    show 2*r+2 = (2*r+1)+1 by omega, Nat.factorial_succ,
    Nat.factorial_succ]
  push_cast
  have hf : (r.factorial : ℝ) ≠ 0 := by positivity
  have hF : ((4*r+3).factorial : ℝ) ≠ 0 := by positivity
  have hR1 : (2*(r : ℝ)+1) ≠ 0 := by positivity
  have hR2 : (2*(r : ℝ)+2) ≠ 0 := by positivity
  field_simp
  <;> ring

end MF21DiscreteLimits
#print axioms MF21DiscreteLimits.integral_pow_one_sub_pow

#print axioms MF21DiscreteLimits.first_column_integral_constant
