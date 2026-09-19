/- Small exact coefficient and degree facts for Marcus Webb's fourth-product minor.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; substantial Codex assistance. -/
import NLA.MF14Degree44.FourthDeterminantBlocks
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
open scoped Matrix
namespace NLA.MF14Degree44

theorem fourth_R_expansion (alpha eta gamma s : ℂ) :
    Rparam alpha eta gamma s =
      C eta * X ^ 3 + C alpha * X ^ 4 + C (1 + alpha * (gamma * s)) * X ^ 5 +
      C (s ^ 2 * alpha ^ 2 + gamma * s) * X ^ 6 +
      C (2 * alpha * s ^ 2) * X ^ 7 + C (s ^ 2) * X ^ 8 := by
  simp [Rparam, Q, map_add, map_mul, map_pow, map_ofNat] <;> ring

theorem fourth_xv_expansion (alpha lam : ℂ) :
    X * (Q alpha + C lam * X ^ 2) = C lam * X ^ 3 + C alpha * X ^ 4 + X ^ 5 := by
  simp [Q] <;> ring

theorem fourth_x2v_expansion (alpha lam : ℂ) :
    X ^ 2 * (Q alpha + C lam * X ^ 2) =
      C lam * X ^ 4 + C alpha * X ^ 5 + X ^ 6 := by
  simp [Q] <;> ring

theorem fourth_qv_expansion (alpha lam : ℂ) :
    Q alpha * (Q alpha + C lam * X ^ 2) =
      C (alpha * lam) * X ^ 5 + C (alpha ^ 2 + lam) * X ^ 6 +
      C (2 * alpha) * X ^ 7 + X ^ 8 := by
  simp [Q, map_add, map_mul, map_pow, map_ofNat] <;> ring

theorem fourth_Q_coeff4 (alpha : ℂ) : (Q alpha).coeff 4 = 1 := by
  simp [Q]

theorem fourth_R_coeff8 (alpha eta gamma s : ℂ) :
    (Rparam alpha eta gamma s).coeff 8 = s ^ 2 := by
  rw [fourth_R_expansion]
  simp only [coeff_add, coeff_C_mul_X_pow]
  <;> norm_num

theorem fourth_Q_degree (alpha : ℂ) : (Q alpha).natDegree ≤ 4 := by
  exact natDegree_add_le_of_degree_le (natDegree_X_pow_le 4)
    ((natDegree_C_mul_le alpha (X ^ 3)).trans ((natDegree_X_pow_le 3).trans (by decide)))

theorem fourth_R_degree (alpha eta gamma s : ℂ) :
    (Rparam alpha eta gamma s).natDegree ≤ 8 := by
  rw [fourth_R_expansion]
  have h (c : ℂ) (k : ℕ) (hk : k ≤ 8) : (C c * X ^ k : Poly).natDegree ≤ 8 :=
    (natDegree_C_mul_le c (X ^ k)).trans ((natDegree_X_pow_le k).trans hk)
  exact (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (h eta 3 (by decide)) (h alpha 4 (by decide))) (h (1 + alpha * (gamma * s)) 5 (by decide))) (h (s ^ 2 * alpha ^ 2 + gamma * s) 6 (by decide))) (h (2 * alpha * s ^ 2) 7 (by decide))) (h (s ^ 2) 8 le_rfl))

theorem fourth_v_degree (alpha lam : ℂ) :
    (Q alpha + C lam * X ^ 2).natDegree ≤ 4 := by
  exact natDegree_add_le_of_degree_le (fourth_Q_degree alpha)
    ((natDegree_C_mul_le lam (X ^ 2)).trans ((natDegree_X_pow_le 2).trans (by decide)))

def fourthCoreIndex (i : Fin 5) : Fin 12 := Fin.natAdd 3 (Fin.castAdd 4 i)
def fourthTailIndex (i : Fin 4) : Fin 12 := Fin.natAdd 3 (Fin.natAdd 5 i)

theorem fourth_middle_column_degree (alpha eta gamma s lam : ℂ) (j : Fin 5) :
    (fourthDerivativeColumns alpha eta gamma s lam (fourthCoreIndex j)).natDegree ≤ 8 := by
  have hq := fourth_Q_degree alpha
  have hr := fourth_R_degree alpha eta gamma s
  have hv := fourth_v_degree alpha lam
  fin_cases j
  · exact hq.trans (by decide)
  · exact hr
  · exact (natDegree_mul_le.trans (Nat.add_le_add
      (natDegree_X_le : (X : Poly).natDegree ≤ 1) hv)).trans (by decide)
  · exact (natDegree_mul_le.trans (Nat.add_le_add (natDegree_X_pow_le 2) hv)).trans (by decide)
  · exact natDegree_mul_le.trans (Nat.add_le_add hq hv)

theorem fourth_tail_column_degree (alpha eta gamma s lam : ℂ) (j : Fin 4) :
    (fourthDerivativeColumns alpha eta gamma s lam (fourthTailIndex j)).natDegree ≤
      (![9, 10, 12, 16] : Fin 4 → ℕ) j := by
  have hq := fourth_Q_degree alpha
  have hr := fourth_R_degree alpha eta gamma s
  fin_cases j
  · exact natDegree_mul_le.trans (Nat.add_le_add
      (natDegree_X_le : (X : Poly).natDegree ≤ 1) hr)
  · exact natDegree_mul_le.trans (Nat.add_le_add (natDegree_X_pow_le 2) hr)
  · exact natDegree_mul_le.trans (Nat.add_le_add hq hr)
  · change (Rparam alpha eta gamma s ^ 2).natDegree ≤ 16
    rw [pow_two]
    exact natDegree_mul_le.trans (Nat.add_le_add hr hr)

theorem fourth_tail_diagonal (alpha eta gamma s lam : ℂ) (i : Fin 4) :
    fourthJacobian alpha eta gamma s lam (fourthTailIndex i) (fourthTailIndex i) =
      (![s ^ 2, s ^ 2, s ^ 2, (s ^ 2) ^ 2] : Fin 4 → ℂ) i := by
  have hr := fourth_R_degree alpha eta gamma s
  fin_cases i
  · change (X * Rparam alpha eta gamma s).coeff 9 = s ^ 2
    simpa [fourth_R_coeff8] using
      (coeff_mul_add_eq_of_natDegree_le (natDegree_X_le : (X : Poly).natDegree ≤ 1) hr)
  · change (X ^ 2 * Rparam alpha eta gamma s).coeff 10 = s ^ 2
    simpa [fourth_R_coeff8] using
      (coeff_mul_add_eq_of_natDegree_le (natDegree_X_pow_le 2 : (X ^ 2 : Poly).natDegree ≤ 2) hr)
  · change (Q alpha * Rparam alpha eta gamma s).coeff 12 = s ^ 2
    simpa [fourth_Q_coeff4, fourth_R_coeff8] using
      (coeff_mul_add_eq_of_natDegree_le (fourth_Q_degree alpha) hr)
  · change (Rparam alpha eta gamma s ^ 2).coeff 16 = (s ^ 2) ^ 2
    simpa only [pow_two, fourth_R_coeff8] using (coeff_mul_add_eq_of_natDegree_le hr hr)

/-- The only dense block has25 small coefficients, rather than144 arbitrary entries. -/
theorem fourth_core_matrix (alpha eta gamma s lam : ℂ) :
    (fourthJacobian alpha eta gamma s lam).submatrix fourthCoreIndex fourthCoreIndex =
      fourthCore alpha eta (s ^ 2) (gamma * s) lam := by
  ext i j
  fin_cases i <;> fin_cases j
  · change (Q alpha).coeff 3 = alpha
    unfold Q
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow]
    <;> norm_num
    <;> ring
  · change (Rparam alpha eta gamma s).coeff 3 = eta
    rw [fourth_R_expansion]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow]
    <;> norm_num
    <;> ring
  · change (X * (Q alpha + C lam * X ^ 2)).coeff 3 = lam
    rw [fourth_xv_expansion]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow]
    <;> norm_num
    <;> ring
  · change (X ^ 2 * (Q alpha + C lam * X ^ 2)).coeff 3 = 0
    rw [fourth_x2v_expansion]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow]
    <;> norm_num
    <;> ring
  · change (Q alpha * (Q alpha + C lam * X ^ 2)).coeff 3 = 0
    rw [fourth_qv_expansion]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow]
    <;> norm_num
    <;> ring
  · change (Q alpha).coeff 4 = 1
    unfold Q
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow]
    <;> norm_num
    <;> ring
  · change (Rparam alpha eta gamma s).coeff 4 = alpha
    rw [fourth_R_expansion]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow]
    <;> norm_num
    <;> ring
  · change (X * (Q alpha + C lam * X ^ 2)).coeff 4 = alpha
    rw [fourth_xv_expansion]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow]
    <;> norm_num
    <;> ring
  · change (X ^ 2 * (Q alpha + C lam * X ^ 2)).coeff 4 = lam
    rw [fourth_x2v_expansion]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow]
    <;> norm_num
    <;> ring
  · change (Q alpha * (Q alpha + C lam * X ^ 2)).coeff 4 = 0
    rw [fourth_qv_expansion]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow]
    <;> norm_num
    <;> ring
  · change (Q alpha).coeff 5 = 0
    unfold Q
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow]
    <;> norm_num
    <;> ring
  · change (Rparam alpha eta gamma s).coeff 5 = 1 + alpha * (gamma * s)
    rw [fourth_R_expansion]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow]
    <;> norm_num
    <;> ring
  · change (X * (Q alpha + C lam * X ^ 2)).coeff 5 = 1
    rw [fourth_xv_expansion]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow]
    <;> norm_num
    <;> ring
  · change (X ^ 2 * (Q alpha + C lam * X ^ 2)).coeff 5 = alpha
    rw [fourth_x2v_expansion]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow]
    <;> norm_num
    <;> ring
  · change (Q alpha * (Q alpha + C lam * X ^ 2)).coeff 5 = alpha * lam
    rw [fourth_qv_expansion]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow]
    <;> norm_num
    <;> ring
  · change (Q alpha).coeff 6 = 0
    unfold Q
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow]
    <;> norm_num
    <;> ring
  · change (Rparam alpha eta gamma s).coeff 6 = s ^ 2 * alpha ^ 2 + gamma * s
    rw [fourth_R_expansion]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow]
    <;> norm_num
    <;> ring
  · change (X * (Q alpha + C lam * X ^ 2)).coeff 6 = 0
    rw [fourth_xv_expansion]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow]
    <;> norm_num
    <;> ring
  · change (X ^ 2 * (Q alpha + C lam * X ^ 2)).coeff 6 = 1
    rw [fourth_x2v_expansion]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow]
    <;> norm_num
    <;> ring
  · change (Q alpha * (Q alpha + C lam * X ^ 2)).coeff 6 = alpha ^ 2 + lam
    rw [fourth_qv_expansion]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow]
    <;> norm_num
    <;> ring
  · change (Q alpha).coeff 8 = 0
    unfold Q
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow]
    <;> norm_num
    <;> ring
  · change (Rparam alpha eta gamma s).coeff 8 = s ^ 2
    rw [fourth_R_expansion]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow]
    <;> norm_num
    <;> ring
  · change (X * (Q alpha + C lam * X ^ 2)).coeff 8 = 0
    rw [fourth_xv_expansion]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow]
    <;> norm_num
    <;> ring
  · change (X ^ 2 * (Q alpha + C lam * X ^ 2)).coeff 8 = 0
    rw [fourth_x2v_expansion]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow]
    <;> norm_num
    <;> ring
  · change (Q alpha * (Q alpha + C lam * X ^ 2)).coeff 8 = 1
    rw [fourth_qv_expansion]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow]
    <;> norm_num
    <;> ring

#print axioms fourth_R_expansion
#assert_trust kernel fourth_R_expansion
#print axioms fourth_middle_column_degree
#assert_trust kernel fourth_middle_column_degree
#print axioms fourth_tail_column_degree
#assert_trust kernel fourth_tail_column_degree
#print axioms fourth_tail_diagonal
#assert_trust kernel fourth_tail_diagonal
#print axioms fourth_core_matrix
#assert_trust kernel fourth_core_matrix
end NLA.MF14Degree44
