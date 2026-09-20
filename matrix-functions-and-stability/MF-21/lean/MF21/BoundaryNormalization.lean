import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Exact endpoint normalization by binomial row operations. All coefficients
of the normalized determinant stay polynomial in the desingularized roots. -/
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open scoped BigOperators
open Finset Matrix
namespace MF21Normalization

def rowShift (m : ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  fun k l => (k.val.choose l.val : ℂ) * (-1 : ℂ)^(k.val-l.val)

theorem rowShift_det (m : ℕ) : (rowShift m).det = 1 := by
  have ht : (rowShift m).IsLowerTriangular := by
    intro i j hij
    simp [rowShift, Nat.choose_eq_zero_of_lt (show i.val < j.val from hij)]
  rw [Matrix.det_of_isLowerTriangular _ ht]
  simp [rowShift]

theorem rowShift_power_sum (m : ℕ) (k : Fin m) (z : ℂ) :
    (∑ l : Fin m, rowShift m k l * z^l.val) = (z-1)^k.val := by
  unfold rowShift
  rw [Fin.sum_univ_eq_sum_range (fun l => (k.val.choose l : ℂ) * (-1 : ℂ)^(k.val-l)*z^l) m]
  have htrunc : (∑ l ∈ range m, (k.val.choose l : ℂ) * (-1 : ℂ)^(k.val-l)*z^l) =
      ∑ l ∈ range (k.val+1), (k.val.choose l : ℂ) * (-1 : ℂ)^(k.val-l)*z^l := by
    symm
    apply sum_subset (range_mono (by omega))
    intro l hl hnot
    have hkl : k.val < l := by have := not_lt.mp (Finset.mem_range.not.mp hnot); omega
    simp [Nat.choose_eq_zero_of_lt hkl]
  rw [htrunc, sub_eq_add_neg, add_pow]
  apply Finset.sum_congr rfl
  intro l hl
  ring

def doubleShift (m : ℕ) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ :=
  Matrix.fromBlocks (rowShift m) 0 0 (rowShift m)

def blockPower (m : ℕ) (z w : Fin m ⊕ Fin m → ℂ) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ :=
  fun i j => Sum.elim (fun k : Fin m => z j^k.val)
    (fun k : Fin m => w j*z j^k.val) i

theorem doubleShift_det (m : ℕ) : (doubleShift m).det = 1 := by
  rw [doubleShift, Matrix.det_fromBlocks_zero₂₁, rowShift_det, one_mul]

theorem doubleShift_mul_blockPower (m : ℕ) (z w : Fin m ⊕ Fin m → ℂ) :
    doubleShift m * blockPower m z w = blockPower m (fun j => z j-1) w := by
  ext i j
  cases i with
  | inl k =>
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, doubleShift, blockPower,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
      zero_mul, Finset.sum_const_zero, add_zero, Sum.elim_inl, Sum.elim_inr]
    exact rowShift_power_sum m k (z j)
  | inr k =>
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, doubleShift, blockPower,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
      zero_mul, Finset.sum_const_zero, zero_add, Sum.elim_inl, Sum.elim_inr]
    calc
      _ = w j * ∑ l : Fin m, rowShift m k l * z j^l.val := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        ring
      _ = _ := by rw [rowShift_power_sum]

/-- Subtracting one from all roots leaves the block-power determinant
unchanged when the column weights remain fixed. -/
theorem blockPower_det_shift (m : ℕ) (z w : Fin m ⊕ Fin m → ℂ) :
    (blockPower m z w).det = (blockPower m (fun j => z j-1) w).det := by
  rw [← doubleShift_mul_blockPower, Matrix.det_mul, doubleShift_det, one_mul]

/-- Exact extraction of every vanishing row factor at a coalescing endpoint. -/
theorem blockPower_det_rescale (m : ℕ) (t : ℂ) (u w : Fin m ⊕ Fin m → ℂ) :
    (blockPower m (fun j => 1+t*u j) w).det =
      t^(2*∑ k ∈ range m, k) * (blockPower m u w).det := by
  rw [blockPower_det_shift]
  have he : blockPower m (fun j => 1+t*u j-1) w =
      fun i j => Sum.elim (fun k : Fin m => t^k.val) (fun k : Fin m => t^k.val) i *
        blockPower m u w i j := by
    ext i j
    cases i <;> simp only [blockPower, Sum.elim_inl, Sum.elim_inr,
      add_sub_cancel_left, mul_pow] <;> ring
  rw [he]
  trans (∏ i : Fin m ⊕ Fin m, Sum.elim (fun k : Fin m => t^k.val)
      (fun k : Fin m => t^k.val) i) * (blockPower m u w).det
  · exact Matrix.det_mul_column
      (Sum.elim (fun k : Fin m => t^k.val) (fun k : Fin m => t^k.val)) (blockPower m u w)
  congr 1
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [← Finset.prod_mul_distrib]
  simp only [← pow_add]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun k => k+k) m]
  simp only [← two_mul]
  rw [Finset.mul_sum]



/-- The extracted order is exactly m(m−1), including m=0 and m=1. -/
theorem blockPower_det_rescale_order (m : ℕ) (t : ℂ) (u w : Fin m ⊕ Fin m → ℂ) :
    (blockPower m (fun j => 1+t*u j) w).det =
      t^(m*(m-1)) * (blockPower m u w).det := by
  rw [blockPower_det_rescale, Nat.mul_comm 2, Finset.sum_range_id_mul_two]

/-- The normalized determinant is a finite sum of smooth coefficients times
products of characteristic roots raised to the same large power. -/
theorem blockPower_det_expansion (m p : ℕ) (u z : Fin m ⊕ Fin m → ℂ) :
    (blockPower m u (fun j => z j^p)).det =
      ∑ σ : Equiv.Perm (Fin m ⊕ Fin m), Equiv.Perm.sign σ •
        ((∏ i : Fin m, u (σ (Sum.inl i))^i.val) *
          (∏ i : Fin m, u (σ (Sum.inr i))^i.val) *
          (∏ i : Fin m, z (σ (Sum.inr i)))^p) := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  simp only [Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro σ hσ
  congr 1
  rw [Fintype.prod_sum_type]
  simp only [blockPower, Sum.elim_inl, Sum.elim_inr]
  rw [Finset.prod_mul_distrib, Finset.prod_pow]
  ring

end MF21Normalization
#print axioms MF21Normalization.rowShift_det
#print axioms MF21Normalization.blockPower_det_shift
#print axioms MF21Normalization.blockPower_det_rescale

#print axioms MF21Normalization.blockPower_det_expansion
