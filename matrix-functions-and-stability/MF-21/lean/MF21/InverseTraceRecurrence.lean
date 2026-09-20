import MF21.ToeplitzGram
import Mathlib.LinearAlgebra.Matrix.Trace

/-! A direct finite-dimensional inverse-trace recurrence. This avoids taking a
continuous Green-kernel limit as a formal assumption. -/
noncomputable section
open scoped BigOperators
open Matrix

namespace MF21InverseTrace

/-- Deleting the first row and column from the inverse gives a rank-one
correction to the inverse of the deleted principal submatrix. -/
theorem inverse_tail (n : ℕ) (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hA : IsUnit A.det) (h00 : (A⁻¹) 0 0 ≠ 0) :
    (A.submatrix Fin.succ Fin.succ)⁻¹ =
      fun i j => (A⁻¹) i.succ j.succ - (A⁻¹) i.succ 0 * (A⁻¹) 0 j.succ / (A⁻¹) 0 0 := by
  apply Matrix.inv_eq_right_inv
  ext i j
  have hij := congrFun (congrFun (Matrix.mul_nonsing_inv A hA) i.succ) j.succ
  have hi0 := congrFun (congrFun (Matrix.mul_nonsing_inv A hA) i.succ) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply,
    Fin.succ_inj, Fin.succ_ne_zero, ite_false] at hij hi0
  change (∑ k : Fin n, A i.succ k.succ *
    ((A⁻¹) k.succ j.succ - (A⁻¹) k.succ 0 * (A⁻¹) 0 j.succ / (A⁻¹) 0 0)) = _
  calc
    _ = (∑ k : Fin n, A i.succ k.succ * (A⁻¹) k.succ j.succ) -
        (∑ k : Fin n, A i.succ k.succ * (A⁻¹) k.succ 0) *
          (A⁻¹) 0 j.succ / (A⁻¹) 0 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, mul_div_assoc, ← mul_assoc,
        Finset.sum_div, Finset.sum_mul]
    _ = (if i = j then 1 else 0) := by
      have hs1 : (∑ k : Fin n, A i.succ k.succ * (A⁻¹) k.succ j.succ) =
          (if i = j then 1 else 0) - A i.succ 0 * (A⁻¹) 0 j.succ := by linarith only [hij]
      have hs2 : (∑ k : Fin n, A i.succ k.succ * (A⁻¹) k.succ 0) =
          -(A i.succ 0 * (A⁻¹) 0 0) := by linarith only [hi0]
      rw [hs1, hs2]
      field_simp [h00]
      ring
    _ = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by rfl


/-- The trace increment is the squared norm of the first inverse column,
divided by its first entry. -/
theorem inverse_trace_step (n : ℕ)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef) :
    (A⁻¹).trace - ((A.submatrix Fin.succ Fin.succ)⁻¹).trace =
      (∑ k : Fin (n+1), ((A⁻¹) k 0) ^ 2) / (A⁻¹) 0 0 := by
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have h00 : (A⁻¹) 0 0 ≠ 0 := ne_of_gt hA.inv.diag_pos
  rw [inverse_tail n A hdet h00]
  have hsym : (A⁻¹).IsSymm := Matrix.isHermitian_iff_isSymm.mp hA.inv.isHermitian
  have hs : ∀ k : Fin (n+1), (A⁻¹) 0 k = (A⁻¹) k 0 := by
    intro k
    exact congrFun (congrFun hsym k) 0
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_succ, Finset.sum_sub_distrib]
  simp_rw [hs]
  rw [← Finset.sum_div]
  have hsq : (∑ k : Fin n, (A⁻¹) k.succ 0 * (A⁻¹) k.succ 0) =
      ∑ k : Fin n, ((A⁻¹) k.succ 0) ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hsq]
  field_simp
  ring

/-- The principal tail of the actual MF-21 matrix has the preceding size. -/
theorem toeplitz_tail (m n : ℕ) :
    (MF21Challenge.toeplitz m (n+1)).submatrix Fin.succ Fin.succ =
      MF21Challenge.toeplitz m n := by
  ext i j
  simp [Matrix.submatrix_apply, MF21Challenge.toeplitz, Nat.dist]

/-- Exact inverse-trace recurrence for the actual Toeplitz matrices. -/
theorem toeplitz_inverse_trace_step (m n : ℕ) :
    ((MF21Challenge.toeplitz m (n+1))⁻¹).trace -
      ((MF21Challenge.toeplitz m n)⁻¹).trace =
      (∑ k : Fin (n+1), (((MF21Challenge.toeplitz m (n+1))⁻¹) k 0) ^ 2) /
        ((MF21Challenge.toeplitz m (n+1))⁻¹) 0 0 := by
  simpa only [toeplitz_tail] using
    inverse_trace_step n _ (MF21Challenge.toeplitz_posDef m (n+1))

end MF21InverseTrace
#print axioms MF21InverseTrace.inverse_tail

#print axioms MF21InverseTrace.inverse_trace_step
#print axioms MF21InverseTrace.toeplitz_inverse_trace_step
