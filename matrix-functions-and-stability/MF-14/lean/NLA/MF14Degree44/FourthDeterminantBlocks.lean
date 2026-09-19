/- Exact small block algebra for Marcus Webb's fourth-product determinant.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; substantial Codex assistance. -/
import NLA.MF14Degree44.Definitions
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Matrix
namespace NLA.MF14Degree44

/-- Simultaneous finite-index reindexing introduces no determinant sign. -/
theorem det_fin_add_of_lower_left_zero {m n : ℕ}
    (A : Matrix (Fin (m + n)) (Fin (m + n)) ℂ)
    (hzero : ∀ i : Fin n, ∀ j : Fin m, A (Fin.natAdd m i) (Fin.castAdd n j) = 0) :
    A.det = (A.submatrix (Fin.castAdd n) (Fin.castAdd n)).det *
      (A.submatrix (Fin.natAdd m) (Fin.natAdd m)).det := by
  let e : Fin m ⊕ Fin n ≃ Fin (m + n) := finSumFinEquiv
  have hblock : A.submatrix e e = Matrix.fromBlocks
      (A.submatrix (Fin.castAdd n) (Fin.castAdd n))
      (A.submatrix (Fin.castAdd n) (Fin.natAdd m))
      0 (A.submatrix (Fin.natAdd m) (Fin.natAdd m)) := by
    ext i j
    cases i <;> cases j
    · rfl
    · rfl
    · exact hzero _ _
    · rfl
  calc
    A.det = (A.submatrix e e).det := (Matrix.det_submatrix_equiv_self e A).symm
    _ = _ := by rw [hblock, Matrix.det_fromBlocks_zero₂₁]

/-- Only the middle five coordinates require a non-triangular determinant. -/
def fourthCore (alpha eta a b lam : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![alpha, eta, lam, 0, 0;
     1, alpha, alpha, lam, 0;
     0, 1 + alpha * b, 1, alpha, alpha * lam;
     0, a * alpha ^ 2 + b, 0, 1, alpha ^ 2 + lam;
     0, a, 0, 0, 1]

/-- Polynomial identity including a=0; sparse recursion never touches a12 determinant. -/
theorem fourth_core_det (alpha eta a b lam : ℂ) :
    (fourthCore alpha eta a b lam).det =
      lam - eta - alpha * lam * (b - a * lam) := by
  simp [fourthCore, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  <;> norm_num
  <;> ring

#print axioms det_fin_add_of_lower_left_zero
#assert_trust kernel det_fin_add_of_lower_left_zero
#print axioms fourth_core_det
#assert_trust kernel fourth_core_det
end NLA.MF14Degree44
