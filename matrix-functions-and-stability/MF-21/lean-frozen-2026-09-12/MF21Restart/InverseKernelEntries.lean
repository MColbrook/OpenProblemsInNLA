import MF21Restart.ToeplitzInverse
import Mathlib.Data.Fin.Rev

/-! Exact entries and reflection, preparing the inverse-kernel limit.
See the prior lock INVERSE_KERNEL_ENTRIES_STATEMENTS.md. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

theorem choose_add_eq_rising_div_factorial (r d : ℕ) :
    ((r + d).choose r : ℝ) =
      (ascPochhammer ℝ r).eval ((d : ℝ) + 1) / (r.factorial : ℝ) := by
  have hf : (r.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
  have hrise : (ascPochhammer ℝ r).eval ((d : ℝ) + 1) =
      (r.factorial : ℝ) * ((r + d).choose r : ℝ) := by
    rw [show (d : ℝ) + 1 = ((d + 1 : ℕ) : ℝ) by norm_cast,
      ascPochhammer_nat_eq_natCast_ascFactorial,
      Nat.ascFactorial_eq_factorial_mul_choose, Nat.cast_mul, Nat.add_comm d r]
  apply (eq_div_iff hf).mpr
  rw [hrise, mul_comm]

theorem toeplitz_inverse_apply_rising (m n : ℕ) (hm : 1 ≤ m) (i j : Fin n) :
    (toeplitz m n)⁻¹ i j =
      ((ascPochhammer ℝ m).eval ((i.val : ℝ) + 1) *
        (ascPochhammer ℝ m).eval ((j.val : ℝ) + 1) /
          ((m - 1).factorial : ℝ) ^ 2) *
        ∑ k : Fin n, if i.val ≤ k.val ∧ j.val ≤ k.val then
          ((ascPochhammer ℝ (m - 1)).eval (((k.val - i.val : ℕ) : ℝ) + 1) *
            (ascPochhammer ℝ (m - 1)).eval (((k.val - j.val : ℕ) : ℝ) + 1)) /
              (ascPochhammer ℝ (2 * m)).eval ((k.val : ℝ) + 1)
          else 0 := by
  classical
  rw [toeplitz_inverse_apply m n hm i j]
  simp_rw [choose_add_eq_rising_div_factorial]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : i.val ≤ k.val ∧ j.val ≤ k.val
  · simp only [if_pos hk, div_eq_mul_inv, pow_two, mul_inv_rev]
    ring
  · simp only [if_neg hk, mul_zero]

theorem toeplitz_submatrix_rev (m n : ℕ) :
    (toeplitz m n).submatrix Fin.revPerm Fin.revPerm = toeplitz m n := by
  ext i j
  simp only [Matrix.submatrix_apply, Fin.revPerm_apply, toeplitz, Fin.val_rev]
  have hdiff : ((n - (i.val + 1) : ℕ) : ℤ) - ((n - (j.val + 1) : ℕ) : ℤ) =
      -((i.val : ℤ) - (j.val : ℤ)) := by
    have hi := i.isLt
    have hj := j.isLt
    omega
  rw [hdiff, fourierCoeff_neg]

theorem toeplitz_inverse_rev (m n : ℕ) (i j : Fin n) :
    (toeplitz m n)⁻¹ i.rev j.rev = (toeplitz m n)⁻¹ i j := by
  have h := Matrix.inv_submatrix_equiv (toeplitz m n) Fin.revPerm Fin.revPerm
  rw [toeplitz_submatrix_rev] at h
  have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) h
  simpa only [Matrix.submatrix_apply, Fin.revPerm_apply] using he.symm

#print axioms choose_add_eq_rising_div_factorial
#print axioms toeplitz_inverse_apply_rising
#print axioms toeplitz_submatrix_rev
#print axioms toeplitz_inverse_rev

end MF21Restart
