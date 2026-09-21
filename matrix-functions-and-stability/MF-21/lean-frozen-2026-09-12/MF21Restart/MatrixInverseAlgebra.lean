import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic

/-! Symbolic finite inverse algebra. All hypotheses are finite matrix
identities to be proved for the actual Toeplitz matrix in the application.
The prior statement lock is MATRIX_INVERSE_ALGEBRA_STATEMENTS.md. -/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem diagonal_reciprocal_mul (w : ι → ℝ) (hw : ∀ i, w i ≠ 0) :
    Matrix.diagonal (fun i => (w i)⁻¹) * Matrix.diagonal w = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact inv_mul_cancel₀ (hw i)

theorem diagonal_mul_reciprocal (w : ι → ℝ) (hw : ∀ i, w i ≠ 0) :
    Matrix.diagonal w * Matrix.diagonal (fun i => (w i)⁻¹) = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact mul_inv_cancel₀ (hw i)

theorem rightInverse_of_weighted_factorization
    (A P R T B W V : Matrix ι ι ℝ)
    (hRP : R * P = 1) (hTB : T * B = 1) (hBT : B * T = 1)
    (hWV : W * V = 1) (hfac : T.transpose * W * T = P * A * P) :
    A * (P * B * V * B.transpose * P) = 1 := by
  calc
    A * (P * B * V * B.transpose * P) =
        (R * P) * A * (P * B * V * B.transpose * P) := by rw [hRP, one_mul]
    _ = R * (P * A * P) * (B * V * B.transpose * P) := by simp only [mul_assoc]
    _ = R * (T.transpose * W * T) * (B * V * B.transpose * P) := by rw [← hfac]
    _ = R * T.transpose * W * (T * B) * V * B.transpose * P := by
      simp only [mul_assoc]
    _ = R * T.transpose * (W * V) * B.transpose * P := by
      rw [hTB, mul_one]
      simp only [mul_assoc]
    _ = R * (T.transpose * B.transpose) * P := by
      rw [hWV, mul_one]
      simp only [mul_assoc]
    _ = R * (B * T).transpose * P := by rw [Matrix.transpose_mul]
    _ = 1 := by rw [hBT, Matrix.transpose_one, mul_one, hRP]

theorem inverse_of_weighted_factorization
    (A P R T B W V : Matrix ι ι ℝ)
    (hRP : R * P = 1) (hTB : T * B = 1) (hBT : B * T = 1)
    (hWV : W * V = 1) (hfac : T.transpose * W * T = P * A * P) :
    A⁻¹ = P * B * V * B.transpose * P :=
  Matrix.inv_eq_right_inv
    (rightInverse_of_weighted_factorization A P R T B W V hRP hTB hBT hWV hfac)

#print axioms diagonal_reciprocal_mul
#print axioms diagonal_mul_reciprocal
#print axioms rightInverse_of_weighted_factorization
#print axioms inverse_of_weighted_factorization

end MF21Restart
