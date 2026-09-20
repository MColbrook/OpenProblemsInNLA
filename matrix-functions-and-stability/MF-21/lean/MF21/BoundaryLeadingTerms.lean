import MF21.BoundaryNormalization
import Mathlib.LinearAlgebra.Vandermonde

/-! Exact extraction of each of the two dominant boundary minors. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace MF21Normalization

/-- Keep only specified columns in the lower ghost block. -/
def maskedBlock (m : ℕ) (z w : Fin m ⊕ Fin m → ℂ)
    (P : Fin m ⊕ Fin m → Prop) [DecidablePred P] :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ :=
  blockPower m z (fun j => if P j then w j else 0)

/-- Selecting the right half of the columns gives the first dominant minor. -/
theorem maskedBlock_right_det (m : ℕ) (z w : Fin m ⊕ Fin m → ℂ) :
    (maskedBlock m z w (fun j => j.isRight)).det =
      (Matrix.vandermonde (fun i => z (Sum.inl i))).det *
      (Matrix.vandermonde (fun i => z (Sum.inr i))).det *
      ∏ i : Fin m, w (Sum.inr i) := by
  have he : maskedBlock m z w (fun j => j.isRight) =
      Matrix.fromBlocks (Matrix.vandermonde (fun i => z (Sum.inl i))).transpose
        (Matrix.vandermonde (fun i => z (Sum.inr i))).transpose 0
        (fun i j : Fin m => w (Sum.inr j)*z (Sum.inr j)^i.val) := by
    ext i j
    cases i <;> cases j <;> simp [maskedBlock, blockPower, Matrix.vandermonde]
  rw [he, Matrix.det_fromBlocks_zero₂₁, Matrix.det_transpose]
  have hd : (Matrix.of (fun i j : Fin m => w (Sum.inr j)*z (Sum.inr j)^i.val)).det =
      (∏ i : Fin m, w (Sum.inr i)) *
        (Matrix.vandermonde (fun i => z (Sum.inr i))).det := by
    exact (Matrix.det_mul_row (fun i : Fin m => w (Sum.inr i))
      (Matrix.vandermonde (fun i => z (Sum.inr i))).transpose).trans
        (by rw [Matrix.det_transpose])
  change _ * (Matrix.of (fun i j : Fin m => w (Sum.inr j)*z (Sum.inr j)^i.val)).det = _
  rw [hd]
  ring

/-- A column transposition gives the other dominant minor with opposite sign. -/
theorem maskedBlock_swap_det (m : ℕ) (a b : Fin m ⊕ Fin m) (hab : a ≠ b)
    (z w : Fin m ⊕ Fin m → ℂ) :
    (maskedBlock m z w (fun j => (Equiv.swap a b j).isRight)).det =
      -((Matrix.vandermonde (fun i => z (Equiv.swap a b (Sum.inl i)))).det *
        (Matrix.vandermonde (fun i => z (Equiv.swap a b (Sum.inr i)))).det *
        ∏ i : Fin m, w (Equiv.swap a b (Sum.inr i))) := by
  classical
  let σ := Equiv.swap a b
  have he : (maskedBlock m z w (fun j => (σ j).isRight)).submatrix id σ =
      maskedBlock m (z ∘ σ) (w ∘ σ) (fun j => j.isRight) := by
    ext i j
    cases i <;> simp [maskedBlock, blockPower, Matrix.submatrix_apply, σ]
  have hd := Matrix.det_permute' σ (maskedBlock m z w (fun j => (σ j).isRight))
  rw [he, maskedBlock_right_det] at hd
  simp only [σ, Equiv.Perm.sign_swap hab, Units.val_neg, Units.val_one, Int.cast_neg,
    Int.cast_one, neg_one_mul] at hd
  simpa only [neg_neg, Function.comp_apply] using congrArg Neg.neg hd.symm

/-- For geometric weights the large exponent factors out of the dominant minor. -/
theorem maskedBlock_right_power (m p : ℕ) (u z : Fin m ⊕ Fin m → ℂ) :
    (maskedBlock m u (fun j => z j^p) (fun j => j.isRight)).det =
      (Matrix.vandermonde (fun i => u (Sum.inl i))).det *
      (Matrix.vandermonde (fun i => u (Sum.inr i))).det *
      (∏ i : Fin m, z (Sum.inr i))^p := by
  rw [maskedBlock_right_det, Finset.prod_pow]

end MF21Normalization
#print axioms MF21Normalization.maskedBlock_right_det
#print axioms MF21Normalization.maskedBlock_swap_det
