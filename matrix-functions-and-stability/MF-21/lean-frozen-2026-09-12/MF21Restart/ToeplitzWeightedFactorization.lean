import MF21Restart.TriangularInverse
import MF21Restart.WeightedBinomialInverse
import MF21Restart.FourierBinomialStencil

/-!
The exact weighted factorization of the actual Fourier Toeplitz matrix.
The one-based positive Pochhammer weights convert the previously proved
weighted binomial sum into Tᵀ W T = P A P. No matrix inverse or limiting
assertion is assumed or concluded here. This is finite algebra toward the
known Duduchava–Roch inverse formula.

The statement lock is `TOEPLITZ_WEIGHTED_FACTORIZATION_STATEMENTS.md`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

/-- The positive-index rising-factorial diagonal; the argument is i+1. -/
def risingFactorialDiagonal (r n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => (ascPochhammer ℝ r).eval ((i.val : ℝ) + 1))

private theorem risingFactorial_eval_succ (r a : ℕ) :
    (ascPochhammer ℝ r).eval ((a : ℝ) + 1) = ((a + 1).ascFactorial r : ℝ) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    ascPochhammer_nat_eq_natCast_ascFactorial ℝ (a + 1) r

private theorem fourierCoeff_nat_binomial (m d : ℕ) :
    fourierCoeff m (d : ℤ) =
      (-1 : ℝ) ^ d * ((2 * m).choose (m + d) : ℝ) := by
  by_cases hd : d ≤ m
  · have h := fourierCoeff_shifted_binomial m (m + d) (by omega)
    have hfreq : ((m + d : ℕ) : ℤ) - (m : ℤ) = (d : ℤ) := by omega
    have hexp : m + (m + d) = 2 * m + d := by omega
    rw [hfreq, hexp, pow_add, pow_mul] at h
    simpa only [neg_one_sq, one_pow, one_mul] using h
  · have hmd : m < d := by omega
    have habs : (m : ℤ) < |(d : ℤ)| := by
      simpa using (show (m : ℤ) < (d : ℤ) by exact_mod_cast hmd)
    have hz : (2 * m).choose (m + d) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [fourierCoeff_support m (d : ℤ) habs, hz, Nat.cast_zero, mul_zero]

private theorem difference_sign_pair (i j k : ℕ) (hji : j ≤ i) (hkj : k ≤ j) :
    (-1 : ℝ) ^ (i - k) * (-1 : ℝ) ^ (j - k) = (-1 : ℝ) ^ (i - j) := by
  calc
    (-1 : ℝ) ^ (i - k) * (-1 : ℝ) ^ (j - k) =
        (-1 : ℝ) ^ ((i - k) + (j - k)) := (pow_add _ _ _).symm
    _ = (-1 : ℝ) ^ ((i - j) + 2 * (j - k)) := by congr 1; omega
    _ = (-1 : ℝ) ^ (i - j) := by
      simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

private theorem weightedDifferenceGram_apply (m n : ℕ) (i j : Fin n) :
    ((differenceUpperMatrix m n).transpose * risingFactorialDiagonal (2 * m) n *
        differenceUpperMatrix m n) i j =
      ∑ k : Fin n, differenceUpperMatrix m n k i *
        (ascPochhammer ℝ (2 * m)).eval ((k.val : ℝ) + 1) *
          differenceUpperMatrix m n k j := by
  rw [Matrix.mul_apply]
  simp only [risingFactorialDiagonal, Matrix.mul_diagonal, Matrix.transpose_apply]

private theorem weightedDifferenceGram_apply_ordered
    (m n : ℕ) (i j : Fin n) (hji : j.val ≤ i.val) :
    ((differenceUpperMatrix m n).transpose * risingFactorialDiagonal (2 * m) n *
        differenceUpperMatrix m n) i j =
      (-1 : ℝ) ^ (i.val - j.val) *
        ∑ k ∈ Finset.Icc 1 (j.val + 1),
          (m.choose (j.val + 1 + (i.val - j.val) - k) : ℝ) *
            (m.choose (j.val + 1 - k) : ℝ) * (k.ascFactorial (2 * m) : ℝ) := by
  classical
  rw [weightedDifferenceGram_apply]
  let term : Fin n → ℝ := fun k =>
    differenceUpperMatrix m n k i *
      (ascPochhammer ℝ (2 * m)).eval ((k.val : ℝ) + 1) *
        differenceUpperMatrix m n k j
  change (∑ k : Fin n, term k) = _
  have hrestrict : (∑ k : Fin n, term k) =
      ∑ k ∈ (Finset.univ : Finset (Fin n)).filter (fun k => k.val ≤ j.val), term k := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k.val ≤ j.val
    · simp only [if_pos hk]
    · simp only [term, differenceUpperMatrix_apply, if_neg hk, mul_zero]
  rw [hrestrict, Finset.mul_sum]
  apply Finset.sum_bij (fun k _ => k.val + 1)
  · intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro a _ b _ hab
    change a.val + 1 = b.val + 1 at hab
    exact Fin.ext (by omega)
  · intro a ha
    have ha' := Finset.mem_Icc.mp ha
    let k : Fin n := ⟨a - 1, by have := j.isLt; omega⟩
    refine ⟨k, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp [k]
      omega
    · dsimp [k]
      omega
  · intro k hk
    have hkj := (Finset.mem_filter.mp hk).2
    have hki : k.val ≤ i.val := hkj.trans hji
    have hidxi : j.val + 1 + (i.val - j.val) - (k.val + 1) = i.val - k.val := by omega
    have hidxj : j.val + 1 - (k.val + 1) = j.val - k.val := by omega
    dsimp only [term]
    rw [hidxi, hidxj]
    simp only [differenceUpperMatrix_apply, if_pos hki, if_pos hkj,
      risingFactorial_eval_succ]
    calc
      _ = ((-1 : ℝ) ^ (i.val - k.val) * (-1 : ℝ) ^ (j.val - k.val)) *
          ((m.choose (i.val - k.val) : ℝ) * (m.choose (j.val - k.val) : ℝ) *
            ((k.val + 1).ascFactorial (2 * m) : ℝ)) := by ring
      _ = _ := by rw [difference_sign_pair i.val j.val k.val hji hkj]

/-- The exact factorization with the actual integral Toeplitz matrix and
the actual finite upper difference matrix, for every matrix size. -/
theorem toeplitz_weighted_factorization (m n : ℕ) (hm : 1 ≤ m) :
    (differenceUpperMatrix m n).transpose *
        risingFactorialDiagonal (2 * m) n * differenceUpperMatrix m n =
      risingFactorialDiagonal m n * toeplitz m n * risingFactorialDiagonal m n := by
  classical
  have hentry (i j : Fin n) (hji : j.val ≤ i.val) :
      ((differenceUpperMatrix m n).transpose * risingFactorialDiagonal (2 * m) n *
          differenceUpperMatrix m n) i j =
        (risingFactorialDiagonal m n * toeplitz m n * risingFactorialDiagonal m n) i j := by
    rw [weightedDifferenceGram_apply_ordered m n i j hji,
      weightedBinomialInverse_identity m (i.val - j.val) (j.val + 1) hm (by omega)]
    have hindex : j.val + 1 + (i.val - j.val) = i.val + 1 := by omega
    rw [hindex]
    simp only [risingFactorialDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul,
      risingFactorial_eval_succ, toeplitz]
    have hfreq : (i.val : ℤ) - (j.val : ℤ) = ((i.val - j.val : ℕ) : ℤ) := by omega
    rw [hfreq, fourierCoeff_nat_binomial]
    ring
  ext i j
  by_cases hji : j.val ≤ i.val
  · exact hentry i j hji
  · have hij : i.val ≤ j.val := by omega
    calc
      ((differenceUpperMatrix m n).transpose * risingFactorialDiagonal (2 * m) n *
          differenceUpperMatrix m n) i j =
          ((differenceUpperMatrix m n).transpose * risingFactorialDiagonal (2 * m) n *
            differenceUpperMatrix m n) j i := by
        simp only [weightedDifferenceGram_apply]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = (risingFactorialDiagonal m n * toeplitz m n * risingFactorialDiagonal m n) j i :=
        hentry j i hij
      _ = (risingFactorialDiagonal m n * toeplitz m n * risingFactorialDiagonal m n) i j := by
        simp only [risingFactorialDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, toeplitz]
        rw [show (j.val : ℤ) - (i.val : ℤ) = -((i.val : ℤ) - (j.val : ℤ)) by ring,
          fourierCoeff_neg]
        ring

#print axioms toeplitz_weighted_factorization

end MF21Restart
