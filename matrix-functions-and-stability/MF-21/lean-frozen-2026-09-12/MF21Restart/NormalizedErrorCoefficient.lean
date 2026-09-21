import MF21Restart.NormalizedQuotient
import MF21Restart.BoundaryProductDecay
import MF21Restart.PhaseZero

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

def boundaryPhaseMultiplier (m : ℕ) (θ : ℝ) : ℂ :=
  Complex.exp (((((m - 1 : ℕ) : ℝ) * θ + 2 * manuscriptPsi m θ : ℝ) : ℂ) * Complex.I)

theorem boundaryPhaseMultiplier_ne_zero (m : ℕ) (θ : ℝ) :
    boundaryPhaseMultiplier m θ ≠ 0 := Complex.exp_ne_zero _

theorem boundaryPhaseMultiplier_contDiffAt (m : ℕ) (hm : 1 ≤ m)
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi) :
    ContDiffAt ℝ ⊤ (boundaryPhaseMultiplier m) θ := by
  have hr : ContDiffAt ℝ ⊤
      (fun t : ℝ => ((m - 1 : ℕ) : ℝ) * t + 2 * manuscriptPsi m t) θ :=
    (contDiffAt_const.mul contDiffAt_id).add
      (contDiffAt_const.mul (manuscriptPsi_contDiffAt m hm θ hθ))
  have hc : ContDiffAt ℝ ⊤
      (fun t : ℝ => (((((m - 1 : ℕ) : ℝ) * t + 2 * manuscriptPsi m t : ℝ) : ℂ) * Complex.I)) θ :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp θ hr).mul contDiffAt_const
  exact ((Complex.contDiff_exp : ContDiff ℂ ⊤ Complex.exp).restrict_scalars ℝ).contDiffAt.comp θ hc

def normalizedErrorCoefficient (m : ℕ) (hm : 1 ≤ m)
    (s : Finset (Fin (2 * m))) (hs : s.card = m) (θ : ℝ) : ℂ :=
  normalizedBoundaryRatio m s (boundaryLeadingZIndices m hm) hs
      (card_boundaryLeadingZIndices m hm) θ /
    (2 * Complex.I * boundaryPhaseMultiplier m θ)

theorem normalizedErrorCoefficient_contDiffAt (m : ℕ) (hm : 2 ≤ m)
    (s : Finset (Fin (2 * m))) (hs : s.card = m)
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi) :
    ContDiffAt ℝ ⊤ (normalizedErrorCoefficient m (by omega) s hs) θ := by
  have hm1 : 1 ≤ m := by omega
  have hden : (2 : ℂ) * Complex.I * boundaryPhaseMultiplier m θ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
      (boundaryPhaseMultiplier_ne_zero m θ)
  convert! (normalizedBoundaryRatio_contDiffAt m hm s _ hs
      (card_boundaryLeadingZIndices m hm1) (boundaryLeadingZIndices_separates m hm1)
      θ hθ).mul ((contDiffAt_const.mul
        (boundaryPhaseMultiplier_contDiffAt m hm1 θ hθ)).inv hden) using 1

theorem normalizedErrorCoefficient_uniform_bound (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Finset (Fin (2 * m)), ∀ hs : s.card = m,
      ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
        ‖normalizedErrorCoefficient m (by omega) s hs θ‖ ≤ C ∧
          ‖deriv (normalizedErrorCoefficient m (by omega) s hs) θ‖ ≤ C := by
  classical
  let S := {s : Finset (Fin (2 * m)) // s.card = m}
  have hall : ∀ s : S, ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      ‖normalizedErrorCoefficient m (by omega) s.val s.property θ‖ ≤ C ∧
        ‖deriv (normalizedErrorCoefficient m (by omega) s.val s.property) θ‖ ≤ C := by
    intro s
    exact exists_pos_bound_with_deriv_of_contDiffAt_on_Icc _
      (normalizedErrorCoefficient_contDiffAt m hm s.val s.property)
  choose cs hpos hbound using hall
  have hsum0 : 0 ≤ ∑ s : S, cs s := Finset.sum_nonneg fun s _ => (hpos s).le
  refine ⟨1 + ∑ s : S, cs s, by linarith, ?_⟩
  intro s hs θ hθ
  have hle : cs (⟨s, hs⟩ : S) ≤ ∑ t : S, cs t :=
    Finset.single_le_sum (fun t _ => (hpos t).le) (Finset.mem_univ _)
  have hb := hbound (⟨s, hs⟩ : S) θ hθ
  exact ⟨by linarith [hb.1], by linarith [hb.2]⟩

#print axioms card_boundaryLeadingZIndices
#print axioms boundaryLeadingZIndices_separates
#print axioms boundaryPhaseMultiplier_contDiffAt
#print axioms normalizedErrorCoefficient_contDiffAt
#print axioms normalizedErrorCoefficient_uniform_bound

end MF21Restart
