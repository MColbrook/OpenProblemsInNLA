import MF21Restart.PhaseMonotonicity
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
An actual analytic neighborhood for the manuscript eta, with uniform
function and derivative bounds on a slightly enlarged closed interval.
Here `⊤ : ℕ∞ω` is the analytic order omega. The statement lock is
`UNIFORM_IMPLICIT_PHASE_STATEMENTS.md`.
-/

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace MF21Restart

/-- Extend the already proved analytic regularity slightly past both
endpoints, and bound the actual eta and its derivative there. -/
theorem manuscriptEta_enlarged_interval_bounds (m : ℕ) (hm : 1 ≤ m) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ y ∈ Set.Icc (-r) (Real.pi + r),
        ContDiffAt ℝ ⊤ (manuscriptEta m) y ∧
        |manuscriptEta m y| ≤ C ∧
        |deriv (manuscriptEta m) y| ≤ C := by
  let U : Set ℝ := {y | ContDiffAt ℝ ⊤ (manuscriptEta m) y}
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    change ContDiffAt ℝ ⊤ (manuscriptEta m) y at hy
    change ∀ᶠ z in 𝓝 y, ContDiffAt ℝ ⊤ (manuscriptEta m) z
    exact hy.eventually (by simp)
  have hsub : Set.Icc (0 : ℝ) Real.pi ⊆ U := by
    intro y hy
    exact manuscriptEta_contDiffAt m hm y hy
  obtain ⟨d₀, hd₀, hball₀⟩ := Metric.isOpen_iff.mp hU 0
    (hsub ⟨le_rfl, Real.pi_pos.le⟩)
  obtain ⟨dπ, hdπ, hballπ⟩ := Metric.isOpen_iff.mp hU Real.pi
    (hsub ⟨Real.pi_pos.le, le_rfl⟩)
  let r : ℝ := min d₀ dπ / 2
  have hr : 0 < r := div_pos (lt_min hd₀ hdπ) (by norm_num)
  have hr₀ : r < d₀ := by
    dsimp [r]
    have := min_le_left d₀ dπ
    linarith
  have hrπ : r < dπ := by
    dsimp [r]
    have := min_le_right d₀ dπ
    linarith
  have henlarged : Set.Icc (-r) (Real.pi + r) ⊆ U := by
    intro y hy
    by_cases hy₀ : 0 ≤ y
    · by_cases hyπ : y ≤ Real.pi
      · exact hsub ⟨hy₀, hyπ⟩
      · apply hballπ
        rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ y - Real.pi)]
        linarith [hy.2]
    · apply hball₀
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_neg (lt_of_not_ge hy₀)]
      linarith [hy.1]
  have hc : ContinuousOn (manuscriptEta m) (Set.Icc (-r) (Real.pi + r)) := by
    intro y hy
    have hreg : ContDiffAt ℝ ⊤ (manuscriptEta m) y := henlarged hy
    exact hreg.continuousAt.continuousWithinAt
  have hd : ContinuousOn (deriv (manuscriptEta m))
      (Set.Icc (-r) (Real.pi + r)) := by
    intro y hy
    have hreg : ContDiffAt ℝ ⊤ (manuscriptEta m) y := henlarged hy
    have h := hreg.continuousAt_fderiv (by simp)
    have he : ContinuousAt (deriv (manuscriptEta m)) y :=
      h.clm_apply continuousAt_const
    exact he.continuousWithinAt
  obtain ⟨C₁, hC₁⟩ := (isCompact_Icc :
    IsCompact (Set.Icc (-r) (Real.pi + r))).exists_bound_of_continuousOn hc
  obtain ⟨C₂, hC₂⟩ := (isCompact_Icc :
    IsCompact (Set.Icc (-r) (Real.pi + r))).exists_bound_of_continuousOn hd
  refine ⟨r, max (max C₁ C₂) 1, hr,
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro y hy
  refine ⟨henlarged hy, ?_, ?_⟩
  · have hv : |manuscriptEta m y| ≤ C₁ := by
      simpa only [Real.norm_eq_abs] using hC₁ y hy
    exact hv.trans ((le_max_left C₁ C₂).trans (le_max_left _ _))
  · have hv : |deriv (manuscriptEta m) y| ≤ C₂ := by
      simpa only [Real.norm_eq_abs] using hC₂ y hy
    exact hv.trans ((le_max_right C₁ C₂).trans (le_max_left _ _))

#print axioms manuscriptEta_enlarged_interval_bounds

end MF21Restart
