import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! A symbolic right-endpoint Riemann-sum error estimate, using the exact
cell oscillation. The prior lock is RIEMANN_CELL_BOUND_STATEMENTS.md. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

theorem riemann_right_sum_error_bound
    (a : ℕ → ℝ) (ha : Monotone a) (L U : ℕ) (hLU : L ≤ U)
    (f : ℝ → ℝ) (ε : ℝ)
    (hf : ∀ k ∈ Finset.Ico L U,
      IntervalIntegrable f MeasureTheory.volume (a k) (a (k + 1)))
    (hosc : ∀ k ∈ Finset.Ico L U, ∀ x ∈ Set.Icc (a k) (a (k + 1)),
      |f (a (k + 1)) - f x| ≤ ε) :
    |(∑ k ∈ Finset.Ico L U, (a (k + 1) - a k) * f (a (k + 1))) -
      ∫ x in a L..a U, f x| ≤ ε * (a U - a L) := by
  have hcell (k : ℕ) (hk : k ∈ Finset.Ico L U) :
      |(a (k + 1) - a k) * f (a (k + 1)) -
          ∫ x in a k..a (k + 1), f x| ≤ ε * (a (k + 1) - a k) := by
    have hle : a k ≤ a (k + 1) := ha (Nat.le_succ k)
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a k) (b := a (k + 1)) (C := ε)
      (f := fun x : ℝ => f (a (k + 1)) - f x) (by
        intro x hx
        rw [Real.norm_eq_abs]
        have hx' : x ∈ Set.Ioc (a k) (a (k + 1)) := by
          simpa only [Set.uIoc_of_le hle] using hx
        exact hosc k hk x ⟨hx'.1.le, hx'.2⟩)
    have hi : (∫ x in a k..a (k + 1), f (a (k + 1)) - f x) =
        (a (k + 1) - a k) * f (a (k + 1)) -
          ∫ x in a k..a (k + 1), f x := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hf k hk),
        intervalIntegral.integral_const, smul_eq_mul]
    rw [hi, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hle)] at hb
    exact hb
  have hsum := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (a := a) (f := f) (μ := MeasureTheory.volume) hLU
      (fun k hk => hf k (Finset.mem_Ico.mpr hk))
  rw [← hsum, ← Finset.sum_sub_distrib]
  calc
    |∑ k ∈ Finset.Ico L U,
        ((a (k + 1) - a k) * f (a (k + 1)) - ∫ x in a k..a (k + 1), f x)| ≤
        ∑ k ∈ Finset.Ico L U,
          |(a (k + 1) - a k) * f (a (k + 1)) - ∫ x in a k..a (k + 1), f x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Ico L U, ε * (a (k + 1) - a k) :=
      Finset.sum_le_sum hcell
    _ = ε * (a U - a L) := by
      rw [← Finset.mul_sum, Finset.sum_Ico_sub (f := a) hLU]

#print axioms riemann_right_sum_error_bound

end MF21Restart
