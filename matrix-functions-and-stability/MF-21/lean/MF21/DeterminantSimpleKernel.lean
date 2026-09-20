import MF21.BoundaryDeterminant
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.Instances.Matrix

/-! A simple zero of a differentiable determinant has exactly one kernel dimension. -/
noncomputable section
open scoped BigOperators
open Matrix Finset
set_option backward.isDefEq.respectTransparency.types false
namespace MF21SimpleKernel

def detContinuous (n : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ Fin n → ℂ) ℂ where
  toMultilinearMap := Matrix.detRowAlternating.toMultilinearMap
  cont := continuous_id.matrix_det

theorem hasDerivAt_det (n : ℕ) (A : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (A' : Matrix (Fin n) (Fin n) ℂ) (x : ℝ) (hA : HasDerivAt A A' x) :
    HasDerivAt (fun t ↦ (A t).det) (∑ i, (Matrix.updateRow (A x) i (A' i)).det) x := by
  let D := (detContinuous n).restrictScalars ℝ
  have hD := (D.hasFDerivAt (A x)).comp_hasDerivAt x hA
  rw [ContinuousMultilinearMap.linearDeriv_apply] at hD
  convert hD using 1 <;> rfl

/-- An invertible single-row replacement forces the original kernel to have
at most one dimension: the replacement row is an injective scalar functional on it. -/
theorem kernel_finrank_le_one_of_updateRow_det_ne_zero (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) (row : Fin n → ℂ)
    (hdet : (Matrix.updateRow A i row).det ≠ 0) :
    Module.finrank ℂ (LinearMap.ker A.mulVecLin) ≤ 1 := by
  let f : LinearMap.ker A.mulVecLin →ₗ[ℂ] ℂ :=
    (dotProductBilin ℂ ℂ row).comp (LinearMap.ker A.mulVecLin).subtype
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    apply Subtype.ext
    have hvA : A.mulVec v.val = 0 := v.property
    have hzero : (Matrix.updateRow A i row).mulVec v.val = 0 := by
      funext j
      by_cases hji : j = i
      · subst j
        change row ⬝ᵥ v.val = 0 at hv
        simpa only [Matrix.mulVec, dotProduct, Matrix.updateRow_self, Pi.zero_apply] using hv
      · simpa only [Matrix.mulVec, dotProduct, Matrix.updateRow_ne hji, Pi.zero_apply] using congrFun hvA j
    have hinj := Matrix.mulVec_injective_of_det_ne_zero hdet
    apply hinj
    simpa only [Submodule.coe_zero, Matrix.mulVec_zero] using hzero
  have hdim := LinearMap.finrank_le_finrank_of_injective hf
  simpa only [Module.finrank_self] using hdim

theorem kernel_finrank_le_one_of_det_deriv_ne_zero (n : ℕ)
    (A : ℝ → Matrix (Fin n) (Fin n) ℂ) (A' : Matrix (Fin n) (Fin n) ℂ)
    (x : ℝ) (d : ℂ) (hA : HasDerivAt A A' x)
    (hd : HasDerivAt (fun t ↦ (A t).det) d x) (hd0 : d ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (A x).mulVecLin) ≤ 1 := by
  have he := hd.unique (hasDerivAt_det n A A' x hA)
  have hs : (∑ i, (Matrix.updateRow (A x) i (A' i)).det) ≠ 0 := by
    rw [← he]
    exact hd0
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  exact kernel_finrank_le_one_of_updateRow_det_ne_zero n (A x) i (A' i) hne

theorem kernel_finrank_eq_one_of_simple_det_zero (n : ℕ)
    (A : ℝ → Matrix (Fin n) (Fin n) ℂ) (A' : Matrix (Fin n) (Fin n) ℂ)
    (x : ℝ) (d : ℂ) (hA : HasDerivAt A A' x)
    (hd : HasDerivAt (fun t ↦ (A t).det) d x) (hd0 : d ≠ 0) (hz : (A x).det = 0) :
    Module.finrank ℂ (LinearMap.ker (A x).mulVecLin) = 1 := by
  apply Nat.le_antisymm (kernel_finrank_le_one_of_det_deriv_ne_zero n A A' x d hA hd hd0)
  apply Submodule.one_le_finrank_iff.mpr
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  intro hbot
  have hm : v ∈ LinearMap.ker (A x).mulVecLin := hv
  rw [hbot] at hm
  exact hv0 hm

set_option backward.isDefEq.respectTransparency false in
theorem kernel_finrank_eq_one_of_differentiable_simple_det_zero (n : ℕ)
    (A : ℝ → Matrix (Fin n) (Fin n) ℂ) (x : ℝ) (d : ℂ)
    (hA : DifferentiableAt ℝ A x) (hd : HasDerivAt (fun t ↦ (A t).det) d x)
    (hd0 : d ≠ 0) (hz : (A x).det = 0) :
    Module.finrank ℂ (LinearMap.ker (A x).mulVecLin) = 1 :=
by
  obtain ⟨Aderiv, hAderiv⟩ := hA
  have hD := hAderiv.hasDerivAt
  exact kernel_finrank_eq_one_of_simple_det_zero n A _ x d hD hd hd0 hz

/-- A simple zero of the actual ghost determinant gives a one-dimensional
true Toeplitz eigenspace, through the exact recurrence correspondence. -/
theorem eigenspace_finrank_eq_one_of_simple_boundary_zero (m n : ℕ) (hm : 0 < m)
    (lam : ℂ) (roots : ℝ → Fin (2 * m) → ℂ) (x : ℝ) (d : ℂ)
    (hinj : Function.Injective (roots x))
    (hr : ∀ j, (MF21Boundary.recurrence m lam).charPoly.IsRoot (roots x j))
    (hA : DifferentiableAt ℝ (fun t ↦ MF21Boundary.boundaryMatrix m n (roots t)) x)
    (hd : HasDerivAt (fun t ↦ (MF21Boundary.boundaryMatrix m n (roots t)).det) d x)
    (hd0 : d ≠ 0) (hz : (MF21Boundary.boundaryMatrix m n (roots x)).det = 0) :
    Module.finrank ℂ (Module.End.eigenspace (MF21Boundary.toeplitz m n).mulVecLin lam) = 1 := by
  rw [← MF21Boundary.boundaryKernel_finrank m n hm lam (roots x) hinj hr]
  exact kernel_finrank_eq_one_of_differentiable_simple_det_zero (2 * m)
    (fun t ↦ MF21Boundary.boundaryMatrix m n (roots t)) x d hA hd hd0 hz

end MF21SimpleKernel
#print axioms MF21SimpleKernel.hasDerivAt_det
#print axioms MF21SimpleKernel.kernel_finrank_eq_one_of_simple_det_zero

#print axioms MF21SimpleKernel.eigenspace_finrank_eq_one_of_simple_boundary_zero
