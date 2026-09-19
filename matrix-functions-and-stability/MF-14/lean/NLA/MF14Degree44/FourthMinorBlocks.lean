/- Structural zeros and diagonal factors for Marcus Webb's fourth-product minor.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; substantial Codex assistance.
No upper-right block entries or factorial12 determinant expansion are evaluated. -/
import NLA.MF14Degree44.FourthMinorCoefficients

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
open scoped BigOperators Matrix
namespace NLA.MF14Degree44

theorem fourth_first_block (alpha eta gamma s lam : ℂ) :
    (fourthJacobian alpha eta gamma s lam).submatrix (Fin.castAdd 9) (Fin.castAdd 9) =
      (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.submatrix, fourthJacobian, fourthDerivativeColumns, fourthRows,
      coeff_one, coeff_X]

theorem fourth_first_lower_zero (alpha eta gamma s lam : ℂ)
    (i : Fin 9) (j : Fin 3) :
    fourthJacobian alpha eta gamma s lam (Fin.natAdd 3 i) (Fin.castAdd 9 j) = 0 := by
  have hrow : 3 ≤ (fourthRows (Fin.natAdd 3 i)).val := by
    fin_cases i <;> decide
  fin_cases j
  · change (1 : Poly).coeff (fourthRows (Fin.natAdd 3 i)).val = 0
    apply coeff_eq_zero_of_natDegree_lt
    simpa using (lt_of_lt_of_le (by decide : 0 < 3) hrow)
  · change (X : Poly).coeff (fourthRows (Fin.natAdd 3 i)).val = 0
    exact coeff_eq_zero_of_natDegree_lt
      (natDegree_X_le.trans_lt (lt_of_lt_of_le (by decide : 1 < 3) hrow))
  · change (X ^ 2 : Poly).coeff (fourthRows (Fin.natAdd 3 i)).val = 0
    exact coeff_eq_zero_of_natDegree_lt
      ((natDegree_X_pow_le 2).trans_lt (lt_of_lt_of_le (by decide : 2 < 3) hrow))

theorem fourth_middle_lower_zero (alpha eta gamma s lam : ℂ)
    (i : Fin 4) (j : Fin 5) :
    fourthJacobian alpha eta gamma s lam (fourthTailIndex i) (fourthCoreIndex j) = 0 := by
  change (fourthDerivativeColumns alpha eta gamma s lam (fourthCoreIndex j)).coeff
    (fourthRows (fourthTailIndex i)).val = 0
  apply coeff_eq_zero_of_natDegree_lt
  apply (fourth_middle_column_degree alpha eta gamma s lam j).trans_lt
  fin_cases i <;> decide

theorem fourth_tail_upper_triangular (alpha eta gamma s lam : ℂ) :
    ((fourthJacobian alpha eta gamma s lam).submatrix
      fourthTailIndex fourthTailIndex).IsUpperTriangular := by
  intro i j hij
  change (fourthDerivativeColumns alpha eta gamma s lam (fourthTailIndex j)).coeff
    (fourthRows (fourthTailIndex i)).val = 0
  apply coeff_eq_zero_of_natDegree_lt
  apply (fourth_tail_column_degree alpha eta gamma s lam j).trans_lt
  fin_cases i <;> fin_cases j <;>
    norm_num [fourthRows, fourthTailIndex] at *
  <;> decide

theorem fourth_tail_det (alpha eta gamma s lam : ℂ) :
    ((fourthJacobian alpha eta gamma s lam).submatrix
      fourthTailIndex fourthTailIndex).det = (s ^ 2) ^ 5 := by
  rw [Matrix.det_of_isUpperTriangular (fourth_tail_upper_triangular alpha eta gamma s lam)]
  change (∏ i : Fin 4, fourthJacobian alpha eta gamma s lam
    (fourthTailIndex i) (fourthTailIndex i)) = (s ^ 2) ^ 5
  simp only [fourth_tail_diagonal]
  simp [Fin.prod_univ_succ] <;> ring

#print axioms fourth_first_block
#assert_trust kernel fourth_first_block
#print axioms fourth_first_lower_zero
#assert_trust kernel fourth_first_lower_zero
#print axioms fourth_middle_lower_zero
#assert_trust kernel fourth_middle_lower_zero
#print axioms fourth_tail_upper_triangular
#assert_trust kernel fourth_tail_upper_triangular
#print axioms fourth_tail_det
#assert_trust kernel fourth_tail_det
end NLA.MF14Degree44
