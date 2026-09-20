import MF21.ActualBoundaryPhase
import MF21.ActualBoundarySimplicity

/-! Ambient smoothness of the nonzero sine normalizer. -/
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped ContDiff Topology BigOperators
open Set
namespace MF21ActualBoundary
open MF21Bulk

private theorem scalar_det_smooth {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℝ → Matrix ι ι ℂ) (x : ℝ)
    (h : ∀ i j, ContDiffAt ℝ ∞ (fun t => M t i j) x) :
    ContDiffAt ℝ ∞ (fun t => (M t).det) x := by
  simp only [Matrix.det_apply']
  apply ContDiffAt.sum
  intro σ _
  apply contDiffAt_const.mul
  apply contDiffAt_prod
  intro i _
  exact h _ _

theorem rootLeadingAmplitude_contDiffAt (m n : ℕ) (hm : 0<m) (x : ℝ)
    (hx : x ∈ Ioo 0 Real.pi) : ContDiffAt ℝ ∞ (rootLeadingAmplitude m n) x := by
  have hb (j : Fin m) := baseRoot_smooth m hm x hx j
  have hi (j : Fin m) : ContDiffAt ℝ ∞ (fun t => (baseRoot m t j)⁻¹) x :=
    (hb j).inv (baseRoot_spec m hm x hx.1 hx.2 j).1
  have hV := scalar_det_smooth (fun t => Matrix.vandermonde (baseRoot m t)) x
    (fun i j => (hb i).pow j.val)
  have hW := scalar_det_smooth (fun t => Matrix.vandermonde (fun i => (baseRoot m t i)⁻¹)) x
    (fun i j => (hi i).pow j.val)
  have hP : ContDiffAt ℝ ∞ (fun t => ∏ j : Fin m, (baseRoot m t j)⁻¹) x :=
    contDiffAt_prod (fun j _ => hi j)
  have he : rootLeadingAmplitude m n = fun t =>
      (Matrix.vandermonde (baseRoot m t)).det *
      (Matrix.vandermonde (fun j => (baseRoot m t j)⁻¹)).det *
      (∏ j : Fin m, (baseRoot m t j)⁻¹)^(n+m) := by
    funext t
    rw [root_coefficient_eq_pair m hm t, root_inverse_product_eq m hm t]
    rfl
  rw [he]
  exact (hV.mul hW).mul (hP.pow (n+m))

theorem sineNormalizer_contDiffAt (m n : ℕ) (hm : 0<m) (x : ℝ)
    (hx : x ∈ Ioo 0 Real.pi) : ContDiffAt ℝ ∞ (sineNormalizer m n) x := by
  have hphase : ContDiffAt ℝ ∞ (secularPhase m n) x :=
    (contDiffAt_const.mul contDiffAt_id).sub (contDiffAt_const.mul
      (psi_contDiffAt m hm x (spectralBase_pos x hx.1 hx.2)))
  exact ((contDiffAt_const.mul (rootLeadingAmplitude_contDiffAt m n hm x hx)).mul
    (unitRoot_contDiff.contDiffAt.comp x hphase))

end MF21ActualBoundary
#print axioms MF21ActualBoundary.sineNormalizer_contDiffAt
