import MF21Restart.InverseKernelContinuity
import MF21Restart.KernelDiagonal
import MF21Restart.TraceIntegral

/-! The checked scalar substitution applies to the actual limiting kernel.
Prior lock: ACTUAL_KERNEL_DIAGONAL_STATEMENTS.md. -/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

def kernelTraceConstant (m : ℕ) : ℝ :=
  ((2 * m - 1).factorial : ℝ) ^ 2 /
    (((4 * m - 1).factorial : ℝ) * ((2 * m - 1 : ℕ) : ℝ) * ((m - 1).factorial : ℝ) ^ 2)

theorem inverseKernel_diagonal_eq (m : ℕ) (hm : 1 ≤ m)
    (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    inverseKernel m x x = x ^ (2 * m - 1) * (1 - x) ^ (2 * m - 1) /
      (((2 * m - 1 : ℕ) : ℝ) * ((m - 1).factorial : ℝ) ^ 2) := by
  have hhigh (x : ℝ) (hx1 : x ≤ 1) (hxhalf : (1 / 2 : ℝ) ≤ x) :
      inverseKernel m x x = x ^ (2 * m - 1) * (1 - x) ^ (2 * m - 1) /
        (((2 * m - 1 : ℕ) : ℝ) * ((m - 1).factorial : ℝ) ^ 2) := by
    have hx0 : 0 < x := by linarith
    rw [inverseKernel_eq_top m x x (by linarith), inverseKernelTop, max_self]
    calc
      (∫ t in x..1, finiteKernelIntegrand m 0 x x t) =
          (x ^ m * x ^ m / ((m - 1).factorial : ℝ) ^ 2) *
            ∫ t in x..1, ((t - x) ^ (m - 1) * (t - x) ^ (m - 1)) / t ^ (2 * m) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t _
        change finiteKernelIntegrand m 0 x x t = _
        rw [finiteKernelIntegrand_zero_step]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ = _ := kernel_diagonal_integral_value m hm x hx0 hx1
  by_cases hhalf : (1 / 2 : ℝ) ≤ x
  · exact hhigh x hx.2 hhalf
  · rw [← inverseKernel_reflection m x x,
      hhigh (1 - x) (by linarith [hx.1]) (by linarith),
      show 1 - (1 - x) = x by ring]
    ring

theorem inverseKernel_diagonal_integral (m : ℕ) (hm : 1 ≤ m) :
    (∫ x in (0 : ℝ)..1, inverseKernel m x x) = kernelTraceConstant m := by
  calc
    (∫ x in (0 : ℝ)..1, inverseKernel m x x) =
        ∫ x in (0 : ℝ)..1, x ^ (2 * m - 1) * (1 - x) ^ (2 * m - 1) /
          (((2 * m - 1 : ℕ) : ℝ) * ((m - 1).factorial : ℝ) ^ 2) := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact inverseKernel_diagonal_eq m hm x
        (by simpa only [Set.uIcc_of_le zero_le_one] using hx)
    _ = _ := diagonal_kernel_integral_value m hm

theorem kernelTraceConstant_pos (m : ℕ) (hm : 1 ≤ m) : 0 < kernelTraceConstant m := by
  have hp := diagonal_kernel_integral_pos m hm
  rw [diagonal_kernel_integral_value m hm] at hp
  exact hp

theorem kernelTraceConstant_rational (m : ℕ) :
    ∃ q : ℚ, kernelTraceConstant m = (q : ℝ) := by
  refine ⟨((2 * m - 1).factorial : ℚ) ^ 2 /
    (((4 * m - 1).factorial : ℚ) * ((2 * m - 1 : ℕ) : ℚ) * ((m - 1).factorial : ℚ) ^ 2), ?_⟩
  simp only [kernelTraceConstant, Rat.cast_div, Rat.cast_pow, Rat.cast_mul, Rat.cast_natCast]

#print axioms inverseKernel_diagonal_eq
#print axioms inverseKernel_diagonal_integral
#print axioms kernelTraceConstant_pos
#print axioms kernelTraceConstant_rational

end MF21Restart
