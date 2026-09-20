import MF21.Definitions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic

/-! Concrete estimates for the exact MF-21 symbol. These are used to turn
the phase error into the eigenvalue error with the endpoint power in (25). -/

open Filter
open scoped Topology ContDiff
noncomputable section
namespace MF21Challenge

theorem symbol_contDiff (m : ℕ) : ContDiff ℝ ∞ (symbol m) := by
  unfold symbol
  fun_prop

theorem symbol_nonneg (m : ℕ) (t : ℝ) : 0 ≤ symbol m t := by
  unfold symbol
  rw [pow_mul]
  positivity

theorem sin_half_abs_le (t : ℝ) :
    |2 * Real.sin (t / 2)| ≤ |t| := by
  calc
    _ = 2 * |Real.sin (t / 2)| := by rw [abs_mul]; norm_num
    _ ≤ 2 * |t / 2| := mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = _ := by rw [abs_div]; norm_num; ring

theorem symbol_abs_le_pow (m : ℕ) (t : ℝ) :
    |symbol m t| ≤ |t| ^ (2 * m) := by
  rw [symbol, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (sin_half_abs_le t) _

theorem sin_half_difference_le (x y : ℝ) :
    |2 * Real.sin (x / 2) - 2 * Real.sin (y / 2)| ≤ |x - y| := by
  calc
    _ = 2 * |Real.sin (x / 2) - Real.sin (y / 2)| := by
      rw [← mul_sub, abs_mul]
      norm_num
    _ ≤ 2 * |x / 2 - y / 2| :=
      mul_le_mul_of_nonneg_left (Real.abs_sin_sub_sin_le _ _) (by norm_num)
    _ = _ := by rw [← sub_div, abs_div]; norm_num; ring

/-- An explicit uniform bound, including the order-2m endpoint zero. -/
theorem symbol_difference_le (m : ℕ) (x y B : ℝ)
    (hx : |x| ≤ B) (hy : |y| ≤ B) :
    |symbol m x - symbol m y| ≤ |x - y| * (2 * m : ℕ) * B ^ (2 * m - 1) := by
  have hB : 0 ≤ B := (abs_nonneg x).trans hx
  calc
    _ ≤ |2 * Real.sin (x / 2) - 2 * Real.sin (y / 2)| * (2 * m : ℕ) *
        max |2 * Real.sin (x / 2)| |2 * Real.sin (y / 2)| ^ (2 * m - 1) :=
      abs_pow_sub_pow_le _ _ _
    _ ≤ _ := by
      have hmax := max_le ((sin_half_abs_le x).trans hx) ((sin_half_abs_le y).trans hy)
      have hn : 0 ≤ max |2 * Real.sin (x / 2)| |2 * Real.sin (y / 2)| :=
        (abs_nonneg _).trans (le_max_left _ _)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (sin_half_difference_le x y) (Nat.cast_nonneg _))
        (pow_le_pow_left₀ hn hmax _)
        (pow_nonneg hn _) (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))

/-- Exact factorization separating the endpoint zero from a continuous factor. -/
theorem symbol_eq_pow_mul_sinc (m : ℕ) (t : ℝ) :
    symbol m t = t ^ (2 * m) * Real.sinc (t / 2) ^ (2 * m) := by
  have hbase : 2 * Real.sin (t / 2) = t * Real.sinc (t / 2) := by
    by_cases ht : t = 0
    · simp [ht]
    · rw [Real.sinc_of_ne_zero (by exact div_ne_zero ht (by norm_num))]
      field_simp
  rw [symbol, hbase, mul_pow]

theorem continuous_symbol_factor (m : ℕ) :
    Continuous (fun t : ℝ => Real.sinc (t / 2) ^ (2 * m)) :=
  (Real.continuous_sinc.comp (continuous_id.div_const 2)).pow _

theorem symbol_factor_tendsto_one (m : ℕ) :
    Tendsto (fun t : ℝ => Real.sinc (t / 2) ^ (2 * m)) (𝓝 0) (𝓝 1) := by
  simpa using (continuous_symbol_factor m).continuousAt.tendsto (x := (0 : ℝ))

end MF21Challenge

#print axioms MF21Challenge.symbol_contDiff
#print axioms MF21Challenge.symbol_difference_le
#print axioms MF21Challenge.symbol_eq_pow_mul_sinc
#print axioms MF21Challenge.symbol_factor_tendsto_one
