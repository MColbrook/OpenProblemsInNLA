import MF21Restart.Definitions
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
The exact symbol derivative and its vanishing bound, used in manuscript
(25). No derivative estimate is a hypothesis. The prior statement lock
is `IMPLICIT_SPECTRAL_ERROR_STATEMENTS.md`.
-/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

theorem symbol_hasDerivAt (m : ℕ) (t : ℝ) :
    HasDerivAt (symbol m)
      (((2 * m : ℕ) : ℝ) * (2 * Real.sin (t / 2)) ^ (2 * m - 1) * Real.cos (t / 2)) t := by
  have hs : HasDerivAt (fun s : ℝ => 2 * Real.sin (s / 2)) (Real.cos (t / 2)) t := by
    convert! (((hasDerivAt_id t).div_const 2).sin.const_mul 2) using 1 <;>
      simp only [id_eq] <;> ring
  exact hs.pow (2 * m)

theorem abs_symbol_deriv_le (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    |deriv (symbol m) t| ≤ ((2 * m : ℕ) : ℝ) * t ^ (2 * m - 1) := by
  have hs : |2 * Real.sin (t / 2)| ≤ t := by
    rw [abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    calc
      2 * |Real.sin (t / 2)| ≤ 2 * |t / 2| :=
        mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
      _ = t := by rw [abs_of_nonneg (by linarith : 0 ≤ t / 2)]; ring
  rw [(symbol_hasDerivAt m t).deriv, abs_mul, abs_mul, abs_pow,
    abs_of_nonneg (Nat.cast_nonneg (2 * m) : (0 : ℝ) ≤ ((2 * m : ℕ) : ℝ))]
  calc
    _ ≤ ((2 * m : ℕ) : ℝ) * |2 * Real.sin (t / 2)| ^ (2 * m - 1) * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)
    _ = ((2 * m : ℕ) : ℝ) * |2 * Real.sin (t / 2)| ^ (2 * m - 1) := mul_one _
    _ ≤ ((2 * m : ℕ) : ℝ) * t ^ (2 * m - 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hs _) (Nat.cast_nonneg _)

/-- Uniform mean-value control on the actual nonnegative angle segment. -/
theorem symbol_difference_le (m : ℕ) (T a b : ℝ)
    (ha : a ∈ Set.Icc (0 : ℝ) T) (hb : b ∈ Set.Icc (0 : ℝ) T) :
    |symbol m a - symbol m b| ≤
      (((2 * m : ℕ) : ℝ) * T ^ (2 * m - 1)) * |a - b| := by
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖deriv (symbol m) t‖ ≤ ((2 * m : ℕ) : ℝ) * T ^ (2 * m - 1) := by
    intro t ht
    rw [Real.norm_eq_abs]
    exact (abs_symbol_deriv_le m t ht.1).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.1 ht.2 _) (Nat.cast_nonneg _))
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (0 : ℝ) T).norm_image_sub_le_of_norm_deriv_le
      (fun t _ => (symbol_hasDerivAt m t).differentiableAt) hbound hb ha

#print axioms symbol_hasDerivAt
#print axioms abs_symbol_deriv_le
#print axioms symbol_difference_le

end MF21Restart
