import MF21Restart.PhasePi
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
noncomputable section

namespace MF21Restart

theorem manuscriptEta_bounded_with_derivative (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      |manuscriptEta m θ| ≤ C ∧ |deriv (manuscriptEta m) θ| ≤ C := by
  have hc : ContinuousOn (manuscriptEta m) (Set.Icc 0 Real.pi) := by
    intro θ hθ
    exact (manuscriptEta_contDiffAt m hm θ hθ).continuousAt.continuousWithinAt
  have hd : ContinuousOn (deriv (manuscriptEta m)) (Set.Icc 0 Real.pi) := by
    intro θ hθ
    have h := (manuscriptEta_contDiffAt m hm θ hθ).continuousAt_fderiv (by simp)
    have he : ContinuousAt (deriv (manuscriptEta m)) θ :=
      h.clm_apply continuousAt_const
    exact he.continuousWithinAt
  obtain ⟨C₁, hC₁⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) Real.pi)).exists_bound_of_continuousOn hc
  obtain ⟨C₂, hC₂⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) Real.pi)).exists_bound_of_continuousOn hd
  refine ⟨max (max C₁ C₂) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro θ hθ
  constructor
  · have hv : |manuscriptEta m θ| ≤ C₁ := by simpa only [Real.norm_eq_abs] using hC₁ θ hθ
    exact hv.trans
      ((le_max_left C₁ C₂).trans (le_max_left _ _))
  · have hv : |deriv (manuscriptEta m) θ| ≤ C₂ := by simpa only [Real.norm_eq_abs] using hC₂ θ hθ
    exact hv.trans
      ((le_max_right C₁ C₂).trans (le_max_left _ _))

def manuscriptPhaseFn (m n : ℕ) (θ : ℝ) : ℝ :=
  (n + 2 : ℝ) * θ - manuscriptEta m θ

theorem manuscriptPhaseFn_zero (m n : ℕ) (hm : 1 ≤ m) :
    manuscriptPhaseFn m n 0 = -(((m : ℝ) - 1) * Real.pi / 2) := by
  simp only [manuscriptPhaseFn, mul_zero, manuscriptEta_zero m hm, zero_sub]

theorem manuscriptPhaseFn_pi (m n : ℕ) (hm : 1 ≤ m) :
    manuscriptPhaseFn m n Real.pi = (n + 1 : ℝ) * Real.pi := by
  rw [manuscriptPhaseFn, manuscriptEta_pi m hm]
  ring

theorem manuscriptPhaseFn_hasDerivAt (m n : ℕ) (hm : 1 ≤ m)
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi) :
    HasDerivAt (manuscriptPhaseFn m n)
      ((n + 2 : ℝ) - deriv (manuscriptEta m) θ) θ := by
  have he := (manuscriptEta_contDiffAt m hm θ hθ).differentiableAt (by simp)
  convert! (((hasDerivAt_id θ).const_mul (n + 2 : ℝ)).sub he.hasDerivAt) using 1 <;>
    simp only [mul_one, manuscriptPhaseFn]

theorem manuscriptPhaseFn_eventual_derivative_bounds (m : ℕ) (hm : 1 ≤ m) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      (n + 2 : ℝ) / 2 ≤ deriv (manuscriptPhaseFn m n) θ ∧
        deriv (manuscriptPhaseFn m n) θ ≤ 2 * (n + 2 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := manuscriptEta_bounded_with_derivative m hm
  refine ⟨Nat.ceil (2 * C), ?_⟩
  intro n hn θ hθ
  have hnreal : (Nat.ceil (2 * C) : ℝ) ≤ n := by exact_mod_cast hn
  have hnC : 2 * C ≤ (n : ℝ) := (Nat.le_ceil (2 * C)).trans hnreal
  have hderiv := abs_le.mp (hbound θ hθ).2
  rw [(manuscriptPhaseFn_hasDerivAt m n hm θ hθ).deriv]
  constructor <;> linarith

theorem manuscriptPhaseFn_eventual_strictMonoOn (m : ℕ) (hm : 1 ≤ m) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      StrictMonoOn (manuscriptPhaseFn m n) (Set.Icc 0 Real.pi) := by
  obtain ⟨N, hN⟩ := manuscriptPhaseFn_eventual_derivative_bounds m hm
  refine ⟨N, ?_⟩
  intro n hn
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 Real.pi)
  · intro θ hθ
    exact (manuscriptPhaseFn_hasDerivAt m n hm θ hθ).continuousAt.continuousWithinAt
  · intro θ hθ
    have hbound := (hN n hn θ (Set.mem_of_mem_of_subset hθ interior_subset)).1
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

#print axioms manuscriptEta_bounded_with_derivative
#print axioms manuscriptPhaseFn_zero
#print axioms manuscriptPhaseFn_pi
#print axioms manuscriptPhaseFn_hasDerivAt
#print axioms manuscriptPhaseFn_eventual_derivative_bounds
#print axioms manuscriptPhaseFn_eventual_strictMonoOn

end MF21Restart
