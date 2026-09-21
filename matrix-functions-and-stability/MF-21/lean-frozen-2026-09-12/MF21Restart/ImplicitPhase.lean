import MF21Restart.EtaNeighborhood
import MF21Restart.UniformImplicitScalar

/-!
The actual manuscript implicit phase from equation (5), constructed
uniformly near `[0,pi] × {0}`. Every scalar inversion hypothesis is
discharged for the already defined manuscript eta. Analytic order `⊤`
implies the joint C-infinity regularity required in Section 4.
-/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

/-- A single actual implicit phase, its uniform neighborhood and size
bound, and uniqueness in a fixed enlarged interval. -/
theorem manuscriptEta_uniform_implicit_phase (m : ℕ) (hm : 1 ≤ m) :
    ∃ r ε C : ℝ, 0 < r ∧ 0 < ε ∧ 0 < C ∧ ∃ Y : ℝ × ℝ → ℝ,
      let D := Set.Ioo (-r / 2) (Real.pi + r / 2) ×ˢ Set.Ioo (-ε) ε
      (∀ p ∈ D, ContDiffAt ℝ ⊤ Y p) ∧
      (∀ p ∈ D, Y p ∈ Set.Ioo (-r) (Real.pi + r) ∧
        Y p = p.1 + p.2 * manuscriptEta m (Y p) ∧
        |Y p - p.1| ≤ C * |p.2|) ∧
      (∀ x ∈ Set.Ioo (-r / 2) (Real.pi + r / 2), Y (x, 0) = x) ∧
      (∀ p ∈ D, ∀ y ∈ Set.Icc (-r) (Real.pi + r),
        y = p.1 + p.2 * manuscriptEta m y → y = Y p) := by
  obtain ⟨r, C, hr, hC, hη⟩ := manuscriptEta_enlarged_interval_bounds m hm
  obtain ⟨ε, hε, Y, hY⟩ :=
    uniform_implicit_scalar (manuscriptEta m) Real.pi r C Real.pi_pos.le hr hC hη
  exact ⟨r, ε, C, hr, hε, hC, Y, hY⟩

#print axioms manuscriptEta_uniform_implicit_phase

end MF21Restart
