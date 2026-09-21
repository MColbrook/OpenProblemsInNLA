import MF21Restart.EigenvalueBridge
import MF21Restart.BoundaryToeplitz
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-!
The missing scalar-field bridge: real characteristic roots are exactly
eigenvalues of the complexified matrix. Composing it with the concrete
boundary criterion identifies the actual one-based sorted eigenvalues.
The precise scope was locked in ROOT_EIGENVALUE_BRIDGE_STATEMENTS.md.
-/

set_option autoImplicit false
noncomputable section
open Matrix

namespace MF21Restart

theorem real_matrix_charpoly_root_iff_complex_eigenvector
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ) :
    A.charpoly.IsRoot lam ↔
      ∃ v : Fin n → ℂ, v ≠ 0 ∧
        A.map Complex.ofReal *ᵥ v = (lam : ℂ) • v := by
  have hmap :
      (A.map Complex.ofReal).charpoly.IsRoot (lam : ℂ) ↔
        A.charpoly.IsRoot lam := by
    change (A.map Complex.ofRealHom).charpoly.IsRoot (Complex.ofRealHom lam) ↔
      A.charpoly.IsRoot lam
    rw [Matrix.charpoly_map]
    exact Polynomial.isRoot_map_iff Complex.ofReal_injective
  refine hmap.symm.trans ?_
  rw [← Matrix.charpoly_mulVecLin,
    ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    refine ⟨v, hv.2, ?_⟩
    simpa only [Matrix.mulVecLin_apply] using hv.apply_eq_smul
  · rintro ⟨v, hv, hAv⟩
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := v)
    apply Module.End.hasEigenvector_iff.mpr
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hv⟩
    simpa only [Matrix.mulVecLin_apply] using hAv

/-- The actual one-based eigenvalue accessor satisfies the boundary criterion. -/
theorem eigenvalue_index_iff_boundaryDeterminant_zero
    (m n : ℕ) (hm : 1 ≤ m) (lam : ℝ) (w : Fin (2 * m) → ℂ)
    (hinj : Function.Injective w) (hnonzero : ∀ i, w i ≠ 0)
    (hvalue : ∀ i, (2 - w i - (w i)⁻¹) ^ m = (lam : ℂ)) :
    (∃ j : ℕ, 1 ≤ j ∧ j ≤ n ∧ eigenvalue m n j = lam) ↔
      (boundaryMatrix m n w).det = 0 := by
  exact (eigenvalue_index_iff_charpoly_root m n lam).trans
    ((real_matrix_charpoly_root_iff_complex_eigenvector n (toeplitz m n) lam).trans
      (boundaryDeterminant_zero_iff_toeplitz_eigenvector
        m n hm (lam : ℂ) w hinj hnonzero hvalue).symm)

/-- Equivalent membership formulation for the unchanged sorted real list. -/
theorem mem_orderedEigenvalueList_iff_boundaryDeterminant_zero
    (m n : ℕ) (hm : 1 ≤ m) (lam : ℝ) (w : Fin (2 * m) → ℂ)
    (hinj : Function.Injective w) (hnonzero : ∀ i, w i ≠ 0)
    (hvalue : ∀ i, (2 - w i - (w i)⁻¹) ^ m = (lam : ℂ)) :
    lam ∈ orderedEigenvalueList m n ↔
      (boundaryMatrix m n w).det = 0 := by
  exact (eigenvalue_index_iff_mem_orderedList m n lam).symm.trans
    (eigenvalue_index_iff_boundaryDeterminant_zero
      m n hm lam w hinj hnonzero hvalue)

#print axioms real_matrix_charpoly_root_iff_complex_eigenvector
#print axioms eigenvalue_index_iff_boundaryDeterminant_zero
#print axioms mem_orderedEigenvalueList_iff_boundaryDeterminant_zero

end MF21Restart
