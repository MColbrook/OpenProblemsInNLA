import MF21.ActualBoundaryDeterminant
import MF21.BoundaryNormalization
import Mathlib.LinearAlgebra.Vandermonde

/-! Exact block-power form of the actual ghost boundary determinant. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace MF21Boundary

/-- The boundary rows split into the left and right ghost blocks. -/
def blockIndex (m : ℕ) : Fin m ⊕ Fin m ≃ Fin (2*m) :=
  finSumFinEquiv.trans (finCongr (Nat.two_mul m).symm)

@[simp] theorem blockIndex_inl_val (m : ℕ) (i : Fin m) :
    (blockIndex m (Sum.inl i)).val = i.val := rfl

@[simp] theorem blockIndex_inr_val (m : ℕ) (i : Fin m) :
    (blockIndex m (Sum.inr i)).val = m+i.val := rfl

theorem boundaryMatrix_block_form (m n : ℕ) (z : Fin (2*m) → ℂ) :
    Matrix.reindex (blockIndex m).symm (blockIndex m).symm (boundaryMatrix m n z) =
      MF21Normalization.blockPower m (z ∘ blockIndex m)
        (fun j => z (blockIndex m j)^(n+m)) := by
  ext i j
  cases i with
  | inl i => simp [Matrix.reindex_apply, boundaryMatrix, ghostIndex,
      MF21Normalization.blockPower, i.isLt]
  | inr i =>
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, boundaryMatrix, ghostIndex,
      blockIndex_inr_val, MF21Normalization.blockPower, Sum.elim_inr,
      Function.comp_apply, show ¬m+i.val<m by omega, if_false]
    rw [show n+(m+i.val)=n+m+i.val by omega, pow_add]

theorem boundary_det_block_form (m n : ℕ) (z : Fin (2*m) → ℂ) :
    (boundaryMatrix m n z).det =
      (MF21Normalization.blockPower m (z ∘ blockIndex m)
        (fun j => z (blockIndex m j)^(n+m))).det := by
  rw [← boundaryMatrix_block_form, Matrix.det_reindex_self]

end MF21Boundary

namespace MF21ActualBoundary

def blockRoots (m : ℕ) (theta : ℝ) : Fin m ⊕ Fin m → ℂ :=
  roots m theta ∘ MF21Boundary.blockIndex m

@[simp] theorem blockRoots_inl (m : ℕ) (theta : ℝ) (j : Fin m) :
    blockRoots m theta (Sum.inl j) = MF21Bulk.baseRoot m theta j := by
  simp [blockRoots, roots, MF21Boundary.blockIndex, MF21Bulk.characteristicRoots,
    finCongr]

@[simp] theorem blockRoots_inr (m : ℕ) (theta : ℝ) (j : Fin m) :
    blockRoots m theta (Sum.inr j) = (MF21Bulk.baseRoot m theta j)⁻¹ := by
  simp [blockRoots, roots, MF21Boundary.blockIndex, MF21Bulk.characteristicRoots,
    finCongr]
  rw [show j.addNat m = Fin.natAdd m j by ext; simp [Nat.add_comm]]
  exact Fin.addCases_right j

theorem determinant_block_form (m n : ℕ) (theta : ℝ) :
    determinant m n theta =
      (MF21Normalization.blockPower m (blockRoots m theta)
        (fun j => blockRoots m theta j^(n+m))).det :=
  MF21Boundary.boundary_det_block_form m n (roots m theta)

/-- Endpoint slopes remove exactly the vanishing order of the boundary determinant. -/
theorem determinant_rescale (m n : ℕ) (theta : ℝ) (t : ℂ)
    (u : Fin m ⊕ Fin m → ℂ)
    (hu : ∀ j, blockRoots m theta j = 1+t*u j) :
    determinant m n theta = t^(m*(m-1)) *
      (MF21Normalization.blockPower m u (fun j => blockRoots m theta j^(n+m))).det := by
  rw [determinant_block_form]
  conv_lhs => arg 1; arg 2; rw [show blockRoots m theta = fun j => 1+t*u j from funext hu]
  exact MF21Normalization.blockPower_det_rescale_order m t u _

end MF21ActualBoundary
#print axioms MF21Boundary.boundary_det_block_form
#print axioms MF21ActualBoundary.determinant_rescale
