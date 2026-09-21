import MF21Restart.Definitions
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
The actual Fourier coefficients of the MF-21 symbol satisfy the discrete
second-difference recurrence and have bandwidth m. The normalization and
integer frequency are those of Definitions.lean. These elementary facts do
not assert the spectral asymptotic expansion or the full MF-21 target.

The scalar integral strategy is adapted from the frozen legacy MF21.lean;
the equality of its cosine-power symbol with the restarted sine-power
definition is proved explicitly below. No legacy module is imported.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

/-- The two formulas for the published symbol agree for every order,
including order zero and both endpoints of the Fourier interval. -/
theorem symbol_eq_cosine_power (m : ℕ) (θ : ℝ) :
    symbol m θ = (2 - 2 * Real.cos θ) ^ m := by
  have hcos := Real.cos_two_mul_eq_one_sub (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at hcos
  have hbase : (2 * Real.sin (θ / 2)) ^ 2 = 2 - 2 * Real.cos θ := by
    rw [hcos]
    ring
  unfold symbol
  rw [pow_mul, hbase]

lemma symbol_succ (m : ℕ) (θ : ℝ) :
    symbol (m + 1) θ = (2 - 2 * Real.cos θ) * symbol m θ := by
  rw [symbol_eq_cosine_power, symbol_eq_cosine_power, pow_succ]
  ring

/-- Multiplication by 2 - 2 cos θ acts by this exact stencil on the
normalized Fourier coefficients; no recurrence is assumed. -/
theorem fourierCoeff_succ (m : ℕ) (k : ℤ) :
    fourierCoeff (m + 1) k =
      2 * fourierCoeff m k - fourierCoeff m (k - 1) -
        fourierCoeff m (k + 1) := by
  have hprod (θ : ℝ) :
      symbol (m + 1) θ * Real.cos ((k : ℝ) * θ) =
        2 * (symbol m θ * Real.cos ((k : ℝ) * θ)) -
          symbol m θ * Real.cos (((k - 1 : ℤ) : ℝ) * θ) -
          symbol m θ * Real.cos (((k + 1 : ℤ) : ℝ) * θ) := by
    have htrig : 2 * Real.cos ((k : ℝ) * θ) * Real.cos θ =
        Real.cos (((k - 1 : ℤ) : ℝ) * θ) +
          Real.cos (((k + 1 : ℤ) : ℝ) * θ) := by
      convert Real.two_mul_cos_mul_cos ((k : ℝ) * θ) θ using 1 <;>
        push_cast <;> ring
    rw [symbol_succ]
    calc
      (2 - 2 * Real.cos θ) * symbol m θ * Real.cos ((k : ℝ) * θ) =
          2 * (symbol m θ * Real.cos ((k : ℝ) * θ)) -
            symbol m θ * (2 * Real.cos ((k : ℝ) * θ) * Real.cos θ) := by ring
      _ = _ := by rw [htrig]; ring
  unfold fourierCoeff
  rw [show (fun θ : ℝ => symbol (m + 1) θ * Real.cos ((k : ℝ) * θ)) =
      (fun θ : ℝ =>
        2 * (symbol m θ * Real.cos ((k : ℝ) * θ)) -
          symbol m θ * Real.cos (((k - 1 : ℤ) : ℝ) * θ) -
          symbol m θ * Real.cos (((k + 1 : ℤ) : ℝ) * θ)) from funext hprod]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul]
  · ring
  all_goals
    apply Continuous.intervalIntegrable
    unfold symbol
    fun_prop

private lemma integral_cos_int_mul_eq_zero (k : ℤ) (hk : k ≠ 0) :
    (∫ θ in -Real.pi..Real.pi, Real.cos ((k : ℝ) * θ)) = 0 := by
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  rw [intervalIntegral.integral_comp_mul_left Real.cos hkr,
    integral_cos]
  simp [mul_neg, Real.sin_neg, Real.sin_int_mul_pi]

/-- The zeroth symbol is the constant 1, with the normalization of the
actual Fourier integral. -/
theorem fourierCoeff_zero (k : ℤ) :
    fourierCoeff 0 k = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    simp [fourierCoeff, symbol]
    field_simp [Real.pi_ne_zero] <;> ring
  · simp [fourierCoeff, symbol, hk, integral_cos_int_mul_eq_zero k hk]

/-- Repeated second differences of the zeroth coefficient cannot produce
frequencies outside the inclusive integer interval [-m,m]. -/
theorem fourierCoeff_support (m : ℕ) (k : ℤ)
    (hk : (m : ℤ) < |k|) :
    fourierCoeff m k = 0 := by
  induction m generalizing k with
  | zero =>
      have hk0 : k ≠ 0 := by
        intro hz
        subst k
        simp at hk
      simp [fourierCoeff_zero, hk0]
  | succ m ih =>
      have hk' : (m : ℤ) + 1 < |k| := by simpa using hk
      have hk0 : (m : ℤ) < |k| := by omega
      have hkm0 : |k| - 1 ≤ |k - 1| := by
        simpa using (abs_sub_abs_le_abs_sub k 1)
      have hkp0 : |k| - 1 ≤ |k + 1| := by
        simpa [sub_neg_eq_add] using (abs_sub_abs_le_abs_sub k (-1))
      have hkm : (m : ℤ) < |k - 1| := by linarith
      have hkp : (m : ℤ) < |k + 1| := by linarith
      rw [fourierCoeff_succ, ih k hk0, ih (k - 1) hkm, ih (k + 1) hkp]
      ring

/-- The defined Toeplitz matrix really has half-bandwidth at most m. -/
theorem toeplitz_entry_eq_zero_of_lt_abs {m n : ℕ} (i j : Fin n)
    (hij : (m : ℤ) < |(i.val : ℤ) - (j.val : ℤ)|) :
    toeplitz m n i j = 0 := by
  exact fourierCoeff_support m ((i.val : ℤ) - (j.val : ℤ)) hij

#print axioms symbol_eq_cosine_power
#print axioms fourierCoeff_succ
#print axioms fourierCoeff_zero
#print axioms fourierCoeff_support
#print axioms toeplitz_entry_eq_zero_of_lt_abs

end MF21Restart
