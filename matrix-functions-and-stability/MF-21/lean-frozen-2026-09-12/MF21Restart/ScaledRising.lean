import MF21Restart.InverseKernelEntries
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.ProperSpace

/-! Polynomial scaling and compact bounds for the actual inverse integrand.
The prior statement lock is SCALED_RISING_STATEMENTS.md. These results do
not yet prove a Riemann-sum limit. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

def scaledRising (r : ℕ) (h x : ℝ) : ℝ :=
  ∏ a ∈ Finset.range r, (x + (a : ℝ) * h)

theorem scaledRising_succ (r : ℕ) (h x : ℝ) :
    scaledRising (r + 1) h x = scaledRising r h x * (x + (r : ℝ) * h) := by
  exact Finset.prod_range_succ _ _

theorem scaledRising_zero_step (r : ℕ) (x : ℝ) :
    scaledRising r 0 x = x ^ r := by
  simp [scaledRising]

theorem scaledRising_scale (r : ℕ) (h x : ℝ) :
    scaledRising r h (h * x) = h ^ r * (ascPochhammer ℝ r).eval x := by
  induction r with
  | zero => simp [scaledRising]
  | succ r ih =>
    rw [scaledRising_succ, ih, ascPochhammer_succ_eval, pow_succ]
    ring

@[fun_prop]
theorem continuous_scaledRising {α : Type*} [TopologicalSpace α]
    (r : ℕ) {h x : α → ℝ} (hh : Continuous h) (hx : Continuous x) :
    Continuous (fun a => scaledRising r (h a) (x a)) := by
  unfold scaledRising
  fun_prop

theorem scaledRising_pos (r : ℕ) (h x : ℝ) (hh : 0 ≤ h) (hx : 0 < x) :
    0 < scaledRising r h x := by
  unfold scaledRising
  apply Finset.prod_pos
  intro a _
  exact add_pos_of_pos_of_nonneg hx (mul_nonneg (Nat.cast_nonneg a) hh)

def finiteKernelIntegrand (m : ℕ) (h x y t : ℝ) : ℝ :=
  (scaledRising m h x * scaledRising m h y *
    scaledRising (m - 1) h (t - x + h) * scaledRising (m - 1) h (t - y + h)) /
      (((m - 1).factorial : ℝ) ^ 2 * scaledRising (2 * m) h t)

theorem finiteKernelIntegrand_zero_step (m : ℕ) (x y t : ℝ) :
    finiteKernelIntegrand m 0 x y t =
      x ^ m * y ^ m * (t - x) ^ (m - 1) * (t - y) ^ (m - 1) /
        (((m - 1).factorial : ℝ) ^ 2 * t ^ (2 * m)) := by
  simp only [finiteKernelIntegrand, add_zero, scaledRising_zero_step]

def kernelParameterBox : Set (Fin 4 → ℝ) :=
  Set.Icc ![0, 0, 0, (1 / 4 : ℝ)] (fun _ => 1)

theorem finiteKernelIntegrand_continuousOn_box (m : ℕ) :
    ContinuousOn (fun p : Fin 4 → ℝ => finiteKernelIntegrand m (p 0) (p 1) (p 2) (p 3))
      kernelParameterBox := by
  have hn : Continuous (fun p : Fin 4 → ℝ =>
      scaledRising m (p 0) (p 1) * scaledRising m (p 0) (p 2) *
        scaledRising (m - 1) (p 0) (p 3 - p 1 + p 0) *
          scaledRising (m - 1) (p 0) (p 3 - p 2 + p 0)) := by fun_prop
  have hd : Continuous (fun p : Fin 4 → ℝ =>
      ((m - 1).factorial : ℝ) ^ 2 * scaledRising (2 * m) (p 0) (p 3)) := by fun_prop
  apply hn.continuousOn.div hd.continuousOn
  intro p hp
  have hh : 0 ≤ p 0 := by simpa only [Matrix.cons_val_zero] using hp.1 0
  have ht : (1 / 4 : ℝ) ≤ p 3 := by
    have ht' := hp.1 (3 : Fin 4)
    change (1 / 4 : ℝ) ≤ p 3 at ht'
    exact ht'
  have hfact : 0 < ((m - 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  exact ne_of_gt (mul_pos (sq_pos_of_pos hfact)
    (scaledRising_pos (2 * m) (p 0) (p 3) hh (by linarith)))

theorem finiteKernelIntegrand_uniformContinuousOn_box (m : ℕ) :
    UniformContinuousOn
      (fun p : Fin 4 → ℝ => finiteKernelIntegrand m (p 0) (p 1) (p 2) (p 3))
      kernelParameterBox :=
  (isCompact_Icc : IsCompact kernelParameterBox).uniformContinuousOn_of_continuous
    (finiteKernelIntegrand_continuousOn_box m)

theorem finiteKernelIntegrand_uniform_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ kernelParameterBox,
      |finiteKernelIntegrand m (p 0) (p 1) (p 2) (p 3)| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact kernelParameterBox).exists_bound_of_continuousOn
    (finiteKernelIntegrand_continuousOn_box m)
  refine ⟨max C 0 + 1, by positivity, ?_⟩
  intro p hp
  have hb : |finiteKernelIntegrand m (p 0) (p 1) (p 2) (p 3)| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC p hp
  exact hb.trans (by linarith [le_max_left C 0])

#print axioms scaledRising_succ
#print axioms scaledRising_zero_step
#print axioms scaledRising_scale
#print axioms continuous_scaledRising
#print axioms scaledRising_pos
#print axioms finiteKernelIntegrand_zero_step
#print axioms finiteKernelIntegrand_continuousOn_box
#print axioms finiteKernelIntegrand_uniformContinuousOn_box
#print axioms finiteKernelIntegrand_uniform_bound

end MF21Restart
