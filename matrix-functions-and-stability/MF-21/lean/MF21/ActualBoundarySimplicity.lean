import MF21.ActualBoundaryDeterminant
import MF21.DeterminantSimpleKernel
import MF21.SpectralSimplicity
import MF21.BulkPhase

open Set Filter
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace MF21ActualBoundary

/-- The actual characteristic roots are smooth throughout the open spectral interval. -/
theorem baseRoot_smooth (m : ℕ) (hm : 0 < m) (theta : ℝ)
    (ht : theta ∈ Ioo 0 Real.pi) (j : Fin m) :
    ContDiffAt ℝ ∞ (fun t ↦ MF21Bulk.baseRoot m t j) theta := by
  by_cases hj : j.val = 0
  · simpa only [MF21Bulk.baseRoot, if_pos hj] using MF21Bulk.unitRoot_contDiff.contDiffAt
  · simpa only [MF21Bulk.baseRoot, if_neg hj, Function.comp_def] using
      (MF21Bulk.stableRoot_contDiffAt (MF21Bulk.omega m j) (MF21Bulk.spectralBase theta)
        (MF21Bulk.spectralBase_pos theta ht.1 ht.2) (MF21Bulk.omega_norm m j)
        (MF21Bulk.omega_ne_one m hm j hj)).comp theta
        MF21Bulk.spectralBase_contDiff.contDiffAt

theorem characteristicRoots_smooth (m : ℕ) (hm : 0 < m) (theta : ℝ)
    (ht : theta ∈ Ioo 0 Real.pi) (j : Fin (m+m)) :
    ContDiffAt ℝ ∞ (fun t ↦ MF21Bulk.characteristicRoots m t j) theta := by
  induction j using Fin.addCases with
  | left j => simpa only [MF21Bulk.characteristicRoots, Fin.addCases_left] using
      baseRoot_smooth m hm theta ht j
  | right j =>
    simp only [MF21Bulk.characteristicRoots, Fin.addCases_right]
    apply ContDiffAt.inv
    · exact baseRoot_smooth m hm theta ht j
    · exact (MF21Bulk.baseRoot_spec m hm theta ht.1 ht.2 j).1

theorem boundaryMatrix_differentiable (m n : ℕ) (hm : 0 < m) (theta : ℝ)
    (ht : theta ∈ Ioo 0 Real.pi) :
    DifferentiableAt ℝ (fun t ↦ MF21Boundary.boundaryMatrix m n (roots m t)) theta := by
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  exact ((characteristicRoots_smooth m hm theta ht (Fin.cast (Nat.two_mul m) j)).pow _).differentiableAt (by simp)

/-- A simple zero of an exactly normalized real secular equation is a simple
indexed Toeplitz eigenvalue. Normalization is required locally, and no root
count or simplicity assumption is inserted. -/
theorem unique_eigenangle_index_of_simple_normalized_zero
    (m n : ℕ) (hm : 0 < m) (F : ℝ → ℝ) (N : ℝ → ℂ)
    (theta : ℝ) (ht : theta ∈ Ioo 0 Real.pi)
    (hF : DifferentiableAt ℝ F theta) (hN : DifferentiableAt ℝ N theta)
    (hidentity : (fun t ↦ determinant m n t) =ᶠ[𝓝 theta] (fun t ↦ N t*(F t : ℂ)))
    (hN0 : N theta ≠ 0) (hzero : F theta = 0) (hdF : deriv F theta ≠ 0)
    (i k : Fin n) (hi : MF21Challenge.eigenangle m n hm i = theta)
    (hk : MF21Challenge.eigenangle m n hm k = theta) : i = k := by
  have hFc : HasDerivAt (fun t ↦ (F t : ℂ)) ((deriv F theta : ℝ) : ℂ) theta :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt theta hF.hasDerivAt
  have hD := (hN.hasDerivAt.mul hFc).congr_of_eventuallyEq hidentity
  have hd0 : deriv N theta*(F theta : ℂ)+N theta*((deriv F theta : ℝ) : ℂ) ≠ 0 := by
    rw [hzero, Complex.ofReal_zero, mul_zero, zero_add]
    exact mul_ne_zero hN0 (by exact_mod_cast hdF)
  have hz : determinant m n theta = 0 := by
    rw [hidentity.eq_of_nhds, hzero, Complex.ofReal_zero, mul_zero]
  have hdim := MF21SimpleKernel.eigenspace_finrank_eq_one_of_simple_boundary_zero
    m n hm (MF21Challenge.symbol m theta) (roots m) theta _
    (roots_injective m hm theta ht.1 ht.2) (roots_charPoly m hm theta ht.1 ht.2)
    (boundaryMatrix_differentiable m n hm theta ht) hD hd0 hz
  exact MF21Challenge.unique_eigenangle_index_of_complex_eigenspace_finrank_one
    m n hm theta hdim i k hi hk

end MF21ActualBoundary

#print axioms MF21ActualBoundary.boundaryMatrix_differentiable
#print axioms MF21ActualBoundary.unique_eigenangle_index_of_simple_normalized_zero
