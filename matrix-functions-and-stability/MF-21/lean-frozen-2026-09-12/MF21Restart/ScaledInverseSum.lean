import MF21Restart.ScaledRising

/-! Exact rescaling of the actual finite Toeplitz inverse. The prior
statement lock is SCALED_INVERSE_SUM_STATEMENTS.md. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

theorem scaled_toeplitz_inverse_eq_sum
    (m n : ℕ) (hm : 1 ≤ m) (h : ℝ) (hh : h ≠ 0) (i j : Fin n) :
    h ^ (2 * m - 1) * (toeplitz m n)⁻¹ i j =
      h * ∑ k : Fin n, if i.val ≤ k.val ∧ j.val ≤ k.val then
        finiteKernelIntegrand m h (h * ((i.val : ℝ) + 1))
          (h * ((j.val : ℝ) + 1)) (h * ((k.val : ℝ) + 1))
        else 0 := by
  classical
  have hpM : h ^ m = h ^ (m - 1) * h := by
    calc
      h ^ m = h ^ ((m - 1) + 1) := by congr 1; omega
      _ = _ := pow_succ _ _
  have hp2M : h ^ (2 * m) = (h ^ (m - 1)) ^ 2 * h ^ 2 := by
    rw [show 2 * m = (m - 1) * 2 + 2 by omega, pow_add, pow_mul]
  have hp2M1 : h ^ (2 * m - 1) = (h ^ (m - 1)) ^ 2 * h := by
    rw [show 2 * m - 1 = (m - 1) * 2 + 1 by omega, pow_add, pow_mul, pow_one]
  rw [toeplitz_inverse_apply_rising m n hm i j,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : i.val ≤ k.val ∧ j.val ≤ k.val
  · rw [if_pos hk, if_pos hk]
    have hx : h * (((k.val - i.val : ℕ) : ℝ) + 1) =
        h * ((k.val : ℝ) + 1) - h * ((i.val : ℝ) + 1) + h := by
      rw [Nat.cast_sub hk.1]
      ring
    have hy : h * (((k.val - j.val : ℕ) : ℝ) + 1) =
        h * ((k.val : ℝ) + 1) - h * ((j.val : ℝ) + 1) + h := by
      rw [Nat.cast_sub hk.2]
      ring
    have hf : ((m - 1).factorial : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hw : (ascPochhammer ℝ (2 * m)).eval ((k.val : ℝ) + 1) ≠ 0 :=
      ne_of_gt (risingFactorial_succ_pos (2 * m) n k)
    unfold finiteKernelIntegrand
    rw [← hx, ← hy]
    simp only [scaledRising_scale, hpM, hp2M, hp2M1]
    field_simp [hf, hw, hh]
    <;> ring
  · simp only [if_neg hk, mul_zero]

#print axioms scaled_toeplitz_inverse_eq_sum

end MF21Restart
