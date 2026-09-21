import MF21Restart.ToeplitzWeightedFactorization
import MF21Restart.MatrixInverseAlgebra

/-! The actual finite inverse of the integral-defined Toeplitz matrix.
The prior statement lock is TOEPLITZ_INVERSE_STATEMENTS.md. No kernel
convergence or spectral asymptotic is assumed here. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

def risingFactorialInvDiagonal (r n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => ((ascPochhammer ℝ r).eval ((i.val : ℝ) + 1))⁻¹)

def manuscriptFiniteInverse (m n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  risingFactorialDiagonal m n * binomialUpperMatrix m n *
    risingFactorialInvDiagonal (2 * m) n * (binomialUpperMatrix m n).transpose *
      risingFactorialDiagonal m n

theorem risingFactorial_succ_pos (r n : ℕ) (i : Fin n) :
    0 < (ascPochhammer ℝ r).eval ((i.val : ℝ) + 1) :=
  ascPochhammer_pos r _ (by positivity)

theorem toeplitz_mul_manuscriptFiniteInverse (m n : ℕ) (hm : 1 ≤ m) :
    toeplitz m n * manuscriptFiniteInverse m n = 1 := by
  have hp (i : Fin n) : (ascPochhammer ℝ m).eval ((i.val : ℝ) + 1) ≠ 0 :=
    ne_of_gt (risingFactorial_succ_pos m n i)
  have hw (i : Fin n) : (ascPochhammer ℝ (2 * m)).eval ((i.val : ℝ) + 1) ≠ 0 :=
    ne_of_gt (risingFactorial_succ_pos (2 * m) n i)
  exact rightInverse_of_weighted_factorization (toeplitz m n)
    (risingFactorialDiagonal m n) (risingFactorialInvDiagonal m n)
    (differenceUpperMatrix m n) (binomialUpperMatrix m n)
    (risingFactorialDiagonal (2 * m) n) (risingFactorialInvDiagonal (2 * m) n)
    (diagonal_reciprocal_mul _ hp) (differenceUpperMatrix_mul_binomial m n)
    (binomialUpperMatrix_mul_difference m n) (diagonal_mul_reciprocal _ hw)
    (toeplitz_weighted_factorization m n hm)

theorem toeplitz_inverse_factorization (m n : ℕ) (hm : 1 ≤ m) :
    (toeplitz m n)⁻¹ = manuscriptFiniteInverse m n :=
  Matrix.inv_eq_right_inv (toeplitz_mul_manuscriptFiniteInverse m n hm)

theorem toeplitz_inverse_apply (m n : ℕ) (hm : 1 ≤ m) (i j : Fin n) :
    (toeplitz m n)⁻¹ i j =
      (ascPochhammer ℝ m).eval ((i.val : ℝ) + 1) *
        (ascPochhammer ℝ m).eval ((j.val : ℝ) + 1) *
          ∑ k : Fin n, if i.val ≤ k.val ∧ j.val ≤ k.val then
            (((m - 1 + (k.val - i.val)).choose (m - 1) : ℝ) *
              ((m - 1 + (k.val - j.val)).choose (m - 1) : ℝ)) /
                (ascPochhammer ℝ (2 * m)).eval ((k.val : ℝ) + 1)
            else 0 := by
  classical
  rw [toeplitz_inverse_factorization m n hm]
  have hentry : manuscriptFiniteInverse m n i j =
      (∑ k : Fin n,
        (ascPochhammer ℝ m).eval ((i.val : ℝ) + 1) * binomialUpperMatrix m n i k *
          ((ascPochhammer ℝ (2 * m)).eval ((k.val : ℝ) + 1))⁻¹ *
            binomialUpperMatrix m n j k) *
              (ascPochhammer ℝ m).eval ((j.val : ℝ) + 1) := by
    unfold manuscriptFiniteInverse risingFactorialDiagonal risingFactorialInvDiagonal
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]
  rw [hentry, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hik : i.val ≤ k.val <;> by_cases hjk : j.val ≤ k.val <;>
    simp only [binomialUpperMatrix_apply m n hm, hik, hjk, and_self,
      and_false, false_and, if_true, if_false, zero_mul, mul_zero]
  simp only [div_eq_mul_inv]
  ring

#print axioms risingFactorial_succ_pos
#print axioms toeplitz_mul_manuscriptFiniteInverse
#print axioms toeplitz_inverse_factorization
#print axioms toeplitz_inverse_apply

end MF21Restart
