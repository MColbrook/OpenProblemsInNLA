import MF21Restart.StableRootDecay
import MF21Restart.RootParameters
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false
noncomputable section

namespace MF21Restart

theorem stable_roots_uniform_exp_decay (m : ℕ) (hm : 2 ≤ m) :
    ∃ c : ℝ, 0 < c ∧ ∀ ell : ℕ, 1 ≤ ell → ell < m →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ Real.pi →
        ‖stableRootCurve (rootKappa m ell) θ‖ ≤ Real.exp (-c * θ) := by
  classical
  haveI : NeZero (m - 1) := ⟨by omega⟩
  have hall : ∀ i : Fin (m - 1), ∃ c : ℝ, 0 < c ∧
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ Real.pi →
        ‖stableRootCurve (rootKappa m (i.val + 1)) θ‖ ≤ Real.exp (-c * θ) := by
    intro i
    exact stableRootCurve_exp_decay _ (rootKappa_re_pos m (i.val + 1) (by omega)
      (by have := i.isLt; omega))
  choose cs hcs hb using hall
  let c : ℝ := Finset.univ.inf' Finset.univ_nonempty cs
  have hc : 0 < c := (Finset.lt_inf'_iff _).mpr (fun i _ => hcs i)
  refine ⟨c, hc, ?_⟩
  intro ell hell hellm θ hθ hθπ
  let i : Fin (m - 1) := ⟨ell - 1, by omega⟩
  have hi : i.val + 1 = ell := by dsimp [i]; omega
  have hcle : c ≤ cs i := Finset.inf'_le cs (Finset.mem_univ i)
  have he : -cs i * θ ≤ -c * θ := by nlinarith
  calc
    ‖stableRootCurve (rootKappa m ell) θ‖ ≤ Real.exp (-cs i * θ) := by
      simpa only [hi] using hb i θ hθ hθπ
    _ ≤ Real.exp (-c * θ) := Real.exp_le_exp.mpr he

theorem stableRootCurve_logarithmic_derivative_bounded (κ : ℂ) (hκ : 0 < κ.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      ‖deriv (stableRootCurve κ) θ / stableRootCurve κ θ‖ ≤ C := by
  have hd := (stableRootCurve_contDiff κ hκ).continuous_deriv (by simp)
  have hr := (stableRootCurve_contDiff κ hκ).continuous
  have hf : Continuous (fun θ : ℝ => deriv (stableRootCurve κ) θ / stableRootCurve κ θ) :=
    hd.div hr (stableRootCurve_ne_zero κ)
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) Real.pi)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro θ hθ
  exact (hC θ hθ).trans (le_max_left _ _)

#print axioms stable_roots_uniform_exp_decay
#print axioms stableRootCurve_logarithmic_derivative_bounded

end MF21Restart
