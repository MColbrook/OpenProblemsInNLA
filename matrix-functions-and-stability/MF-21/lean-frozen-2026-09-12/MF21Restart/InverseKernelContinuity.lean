import MF21Restart.InverseKernelGridTop
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The explicit upper formula and its reflection glue continuously.
Prior lock: INVERSE_KERNEL_CONTINUITY_STATEMENTS.md. -/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

theorem finiteKernelIntegrand_symm (m : ℕ) (h x y t : ℝ) :
    finiteKernelIntegrand m h x y t = finiteKernelIntegrand m h y x t := by
  unfold finiteKernelIntegrand
  ring

def inverseKernelTopExtension (m : ℕ) (x y : ℝ) : ℝ :=
  ∫ t in max x y..1, finiteKernelIntegrand m 0 x y (max t (1 / 4))

theorem inverseKernelTopExtension_symm (m : ℕ) (x y : ℝ) :
    inverseKernelTopExtension m x y = inverseKernelTopExtension m y x := by
  unfold inverseKernelTopExtension
  rw [max_comm y x]
  apply intervalIntegral.integral_congr
  intro t _
  exact finiteKernelIntegrand_symm m 0 x y (max t (1 / 4))

theorem inverseKernelTopExtension_eq_top (m : ℕ) (x y : ℝ) (hxy : 1 ≤ x + y) :
    inverseKernelTopExtension m x y = inverseKernelTop m x y := by
  have hmax : (1 / 4 : ℝ) ≤ max x y := by
    linarith [le_max_left x y, le_max_right x y]
  unfold inverseKernelTopExtension inverseKernelTop
  apply intervalIntegral.integral_congr
  intro t ht
  have htq : (1 / 4 : ℝ) ≤ t :=
    (le_min hmax (by norm_num : (1 / 4 : ℝ) ≤ 1)).trans ht.1
  change finiteKernelIntegrand m 0 x y (max t (1 / 4)) = finiteKernelIntegrand m 0 x y t
  rw [max_eq_left htq]

theorem continuous_inverseKernelTopExtension (m : ℕ) :
    Continuous (fun p : ℝ × ℝ => inverseKernelTopExtension m p.1 p.2) := by
  have hf : Continuous (Function.uncurry (fun p : ℝ × ℝ =>
      fun t : ℝ => finiteKernelIntegrand m 0 p.1 p.2 (max t (1 / 4)))) := by
    change Continuous (fun p : (ℝ × ℝ) × ℝ =>
      finiteKernelIntegrand m 0 p.1.1 p.1.2 (max p.2 (1 / 4)))
    unfold finiteKernelIntegrand
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro p
      have hf : ((m - 1).factorial : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have ht : 0 < max p.2 (1 / 4 : ℝ) :=
        lt_of_lt_of_le (by norm_num) (le_max_right _ _)
      exact mul_ne_zero (pow_ne_zero 2 hf)
        (ne_of_gt (scaledRising_pos (2 * m) 0 (max p.2 (1 / 4)) le_rfl ht))
  have hc := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := MeasureTheory.volume) (a₀ := (1 : ℝ)) hf
    (continuous_fst.max continuous_snd)
  have heq : (fun p : ℝ × ℝ => inverseKernelTopExtension m p.1 p.2) =
      (fun p : ℝ × ℝ => -(∫ t in (1 : ℝ)..max p.1 p.2,
        finiteKernelIntegrand m 0 p.1 p.2 (max t (1 / 4)))) := by
    funext p
    exact intervalIntegral.integral_symm 1 (max p.1 p.2)
  rw [heq]
  exact hc.neg

def inverseKernel (m : ℕ) (x y : ℝ) : ℝ :=
  if 1 ≤ x + y then inverseKernelTopExtension m x y
  else inverseKernelTopExtension m (1 - x) (1 - y)

theorem inverseKernel_eq_top (m : ℕ) (x y : ℝ) (hxy : 1 ≤ x + y) :
    inverseKernel m x y = inverseKernelTop m x y := by
  rw [inverseKernel, if_pos hxy]
  exact inverseKernelTopExtension_eq_top m x y hxy

theorem continuous_inverseKernel (m : ℕ) :
    Continuous (fun p : ℝ × ℝ => inverseKernel m p.1 p.2) := by
  have hc := continuous_inverseKernelTopExtension m
  have hr : Continuous (fun p : ℝ × ℝ =>
      inverseKernelTopExtension m (1 - p.1) (1 - p.2)) :=
    hc.comp ((continuous_const.sub continuous_fst).prodMk
      (continuous_const.sub continuous_snd))
  apply hc.if_le hr continuous_const (continuous_fst.add continuous_snd)
  intro p hp
  change 1 = p.1 + p.2 at hp
  have hx : 1 - p.1 = p.2 := by linarith
  have hy : 1 - p.2 = p.1 := by linarith
  rw [hx, hy]
  exact inverseKernelTopExtension_symm m p.1 p.2

theorem inverseKernel_symm (m : ℕ) (x y : ℝ) :
    inverseKernel m x y = inverseKernel m y x := by
  unfold inverseKernel
  rw [add_comm y x]
  split_ifs
  · exact inverseKernelTopExtension_symm m x y
  · exact inverseKernelTopExtension_symm m (1 - x) (1 - y)

theorem inverseKernel_reflection (m : ℕ) (x y : ℝ) :
    inverseKernel m (1 - x) (1 - y) = inverseKernel m x y := by
  by_cases he : x + y = 1
  · have hxy : 1 ≤ x + y := he.ge
    have hr : 1 ≤ (1 - x) + (1 - y) := by linarith
    rw [inverseKernel, if_pos hr, inverseKernel, if_pos hxy]
    rw [show 1 - x = y by linarith, show 1 - y = x by linarith]
    exact inverseKernelTopExtension_symm m y x
  · by_cases hlt : x + y < 1
    · have hr : 1 ≤ (1 - x) + (1 - y) := by linarith
      rw [inverseKernel, if_pos hr, inverseKernel, if_neg (not_le.mpr hlt)]
    · have hxy : 1 ≤ x + y := le_of_not_gt hlt
      have hr : ¬1 ≤ (1 - x) + (1 - y) := by intro h; apply he; linarith
      rw [inverseKernel, if_neg hr, inverseKernel, if_pos hxy]
      rw [show 1 - (1 - x) = x by ring, show 1 - (1 - y) = y by ring]

def kernelUnitSquare : Set (ℝ × ℝ) := Set.Icc (0, 0) (1, 1)

theorem inverseKernel_uniformContinuousOn (m : ℕ) :
    UniformContinuousOn (fun p : ℝ × ℝ => inverseKernel m p.1 p.2) kernelUnitSquare :=
  (isCompact_Icc : IsCompact kernelUnitSquare).uniformContinuousOn_of_continuous
    (continuous_inverseKernel m).continuousOn

#print axioms finiteKernelIntegrand_symm
#print axioms inverseKernelTopExtension_symm
#print axioms inverseKernelTopExtension_eq_top
#print axioms continuous_inverseKernelTopExtension
#print axioms inverseKernel_eq_top
#print axioms continuous_inverseKernel
#print axioms inverseKernel_symm
#print axioms inverseKernel_reflection
#print axioms inverseKernel_uniformContinuousOn

end MF21Restart
