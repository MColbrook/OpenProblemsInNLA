import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Instances.Matrix

/-!
A differentiable complex matrix curve has zero determinant derivative at
any point where its complex kernel has dimension at least two. The exact
derivative is derived from the continuous multilinear determinant; every
row-replacement term is then singular by the dimension theorem.
DETERMINANT_MULTIPLICITY_STATEMENTS.md fixes these statements first.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix

namespace MF21Restart

/-- One extra scalar equation cannot annihilate a kernel of dimension at least two. -/
theorem det_updateRow_eq_zero_of_two_le_finrank_ker
    (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ)
    (hker : 2 ≤ Module.finrank ℂ (LinearMap.ker A.mulVecLin))
    (i : Fin N) (b : Fin N → ℂ) :
    (A.updateRow i b).det = 0 := by
  let f : (LinearMap.ker A.mulVecLin) →ₗ[ℂ] ℂ :=
    (dotProductBilin ℂ ℂ b).comp (LinearMap.ker A.mulVecLin).subtype
  have hdim : Module.finrank ℂ ℂ <
      Module.finrank ℂ (LinearMap.ker A.mulVecLin) := by
    simpa only [Module.finrank_self] using
      (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hker)
  have hfker : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfker
  have hAv : A *ᵥ (v : Fin N → ℂ) = 0 := by
    simpa only [Matrix.mulVecLin_apply] using (LinearMap.mem_ker.mp v.property)
  have hb : b ⬝ᵥ (v : Fin N → ℂ) = 0 := LinearMap.mem_ker.mp hv
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨(v : Fin N → ℂ), ?_, ?_⟩
  · intro hvzero
    apply hvne
    exact Subtype.ext hvzero
  · rw [Matrix.updateRow_mulVec, hAv, hb]
    simp

private def determinantContinuousMultilinear (N : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin N => Fin N → ℂ) ℂ :=
  { (Matrix.detRowAlternating : (Fin N → ℂ) [⋀^Fin N]→ₗ[ℂ] ℂ).toMultilinearMap with
    cont := continuous_id.matrix_det }

private lemma determinantContinuousMultilinear_apply (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    determinantContinuousMultilinear N A = A.det := rfl

/-- The actual derivative formula, obtained from the multilinear chain rule. -/
theorem hasDerivAt_det_curve
    (N : ℕ) (M : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (M' : Matrix (Fin N) (Fin N) ℂ) (θ : ℝ)
    (hM : HasDerivAt M M' θ) :
    HasDerivAt (fun t : ℝ => (M t).det)
      (∑ i : Fin N, ((M θ).updateRow i (M' i)).det) θ := by
  let D := determinantContinuousMultilinear N
  have h := ((D.hasFDerivAt (M θ)).restrictScalars ℝ).comp_hasDerivAt θ hM
  change HasDerivAt (fun t : ℝ => (M t).det) (D.linearDeriv (M θ) M') θ at h
  erw [ContinuousMultilinearMap.linearDeriv_apply] at h
  change HasDerivAt (fun t : ℝ => (M t).det)
    (∑ i : Fin N, ((M θ).updateRow i (M' i)).det) θ at h
  exact h

/-- The determinant derivative vanishes at every point with complex nullity at least two. -/
theorem hasDerivAt_det_zero_of_two_le_finrank_ker
    (N : ℕ) (M : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (M' : Matrix (Fin N) (Fin N) ℂ) (θ : ℝ)
    (hM : HasDerivAt M M' θ)
    (hker : 2 ≤ Module.finrank ℂ (LinearMap.ker (M θ).mulVecLin)) :
    HasDerivAt (fun t : ℝ => (M t).det) 0 θ := by
  have hsum : (∑ i : Fin N, ((M θ).updateRow i (M' i)).det) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact det_updateRow_eq_zero_of_two_le_finrank_ker N (M θ) hker i (M' i)
  simpa only [hsum] using hasDerivAt_det_curve N M M' θ hM

/-- Entrywise differentiation suffices; the finite Pi derivatives are assembled explicitly. -/
theorem hasDerivAt_det_zero_of_entrywise_deriv_and_two_le_finrank_ker
    (N : ℕ) (M : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (M' : Matrix (Fin N) (Fin N) ℂ) (θ : ℝ)
    (hM : ∀ i j, HasDerivAt (fun t : ℝ => M t i j) (M' i j) θ)
    (hker : 2 ≤ Module.finrank ℂ (LinearMap.ker (M θ).mulVecLin)) :
    HasDerivAt (fun t : ℝ => (M t).det) 0 θ := by
  apply hasDerivAt_det_zero_of_two_le_finrank_ker N M M' θ ?_ hker
  exact hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => hM i j

#print axioms det_updateRow_eq_zero_of_two_le_finrank_ker
#print axioms hasDerivAt_det_curve
#print axioms hasDerivAt_det_zero_of_two_le_finrank_ker
#print axioms hasDerivAt_det_zero_of_entrywise_deriv_and_two_le_finrank_ker

end MF21Restart
