import MF21Restart.CharacteristicSublist
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
noncomputable section

namespace MF21Restart

def normalizedBoundaryRatio (m : ℕ) (s t : Finset (Fin (2 * m)))
    (hs : s.card = m) (ht : t.card = m) (θ : ℝ) : ℂ :=
  normalizedBoundaryCoefficient m s hs θ / normalizedBoundaryCoefficient m t ht θ

theorem boundaryCoefficient_ratio_eq_normalized (m : ℕ)
    (s t : Finset (Fin (2 * m))) (hs : s.card = m) (ht : t.card = m)
    (θ : ℝ) (hθ : θ ≠ 0) :
    boundaryCoefficient m (characteristicRoots m θ) s /
        boundaryCoefficient m (characteristicRoots m θ) t =
      normalizedBoundaryRatio m s t hs ht θ := by
  rw [boundaryCoefficient_eq_pow_mul_normalized m s hs,
    boundaryCoefficient_eq_pow_mul_normalized m t ht]
  exact mul_div_mul_left _ _ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hθ))

theorem normalizedBoundaryRatio_contDiffAt (m : ℕ) (hm : 2 ≤ m)
    (s t : Finset (Fin (2 * m))) (hs : s.card = m) (ht : t.card = m)
    (hsep : ∀ a b : Fin (2 * m), a.val = m - 1 → b.val = m → (a ∈ t ↔ b ∉ t))
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi) :
    ContDiffAt ℝ ⊤ (normalizedBoundaryRatio m s t hs ht) θ := by
  convert! (normalizedBoundaryCoefficient_contDiff m hm s hs).contDiffAt.mul
      ((normalizedBoundaryCoefficient_contDiff m hm t ht).contDiffAt.inv
        (normalizedBoundaryCoefficient_ne_zero_on_Icc m hm t ht hsep θ hθ)) using 1

theorem exists_pos_bound_with_deriv_of_contDiffAt_on_Icc
    (f : ℝ → ℂ) (hf : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi, ContDiffAt ℝ ⊤ f θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      ‖f θ‖ ≤ C ∧ ‖deriv f θ‖ ≤ C := by
  have hc : ContinuousOn f (Set.Icc 0 Real.pi) :=
    fun θ hθ => (hf θ hθ).continuousAt.continuousWithinAt
  have hd : ContinuousOn (deriv f) (Set.Icc 0 Real.pi) := by
    intro θ hθ
    have h := (hf θ hθ).continuousAt_fderiv (by simp)
    have he : ContinuousAt (deriv f) θ := h.clm_apply continuousAt_const
    exact he.continuousWithinAt
  obtain ⟨C₁, hC₁⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) Real.pi)).exists_bound_of_continuousOn hc
  obtain ⟨C₂, hC₂⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) Real.pi)).exists_bound_of_continuousOn hd
  refine ⟨max (max C₁ C₂) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro θ hθ
  exact ⟨(hC₁ θ hθ).trans ((le_max_left C₁ C₂).trans (le_max_left _ _)),
    (hC₂ θ hθ).trans ((le_max_right C₁ C₂).trans (le_max_left _ _))⟩

theorem normalizedBoundaryRatio_bounded_with_derivative (m : ℕ) (hm : 2 ≤ m)
    (s t : Finset (Fin (2 * m))) (hs : s.card = m) (ht : t.card = m)
    (hsep : ∀ a b : Fin (2 * m), a.val = m - 1 → b.val = m → (a ∈ t ↔ b ∉ t)) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      ‖normalizedBoundaryRatio m s t hs ht θ‖ ≤ C ∧
        ‖deriv (normalizedBoundaryRatio m s t hs ht) θ‖ ≤ C :=
  exists_pos_bound_with_deriv_of_contDiffAt_on_Icc _
    (normalizedBoundaryRatio_contDiffAt m hm s t hs ht hsep)

#print axioms boundaryCoefficient_ratio_eq_normalized
#print axioms normalizedBoundaryRatio_contDiffAt
#print axioms exists_pos_bound_with_deriv_of_contDiffAt_on_Icc
#print axioms normalizedBoundaryRatio_bounded_with_derivative

end MF21Restart
