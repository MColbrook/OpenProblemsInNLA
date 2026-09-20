import MF21.ToeplitzGram
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.Nat.Choose.Basic

/-! Exact first-column construction for the inverse of the MF-21 Toeplitz
matrix. The order is written m=r+1 to avoid truncated subtraction in the
polynomial whose degree is 2m-1. -/

set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Polynomial Finset Matrix

namespace MF21FirstColumn

def normalizer (r n : ℕ) : ℝ :=
  (r.factorial : ℝ) * (ascPochhammer ℝ (r + 1)).eval ((n : ℝ) + (r + 1))

def boundaryPolynomial (r n : ℕ) : ℝ[X] :=
  C (normalizer r n)⁻¹ *
    ((ascPochhammer ℝ r).comp (X + 1) *
      (ascPochhammer ℝ (r + 1)).comp (C (n : ℝ) - X))

def value (r n : ℕ) (x : ℝ) : ℝ := (boundaryPolynomial r n).eval x

theorem normalizer_pos (r n : ℕ) : 0 < normalizer r n := by
  unfold normalizer
  apply mul_pos (by exact_mod_cast Nat.factorial_pos r)
  apply ascPochhammer_pos
  positivity

theorem value_formula (r n : ℕ) (x : ℝ) :
    value r n x = (normalizer r n)⁻¹ *
      ((ascPochhammer ℝ r).eval (x + 1) *
        (ascPochhammer ℝ (r + 1)).eval ((n : ℝ) - x)) := by
  simp [value, boundaryPolynomial]

theorem boundaryPolynomial_degree (r n : ℕ) :
    (boundaryPolynomial r n).natDegree < 2 * (r + 1) := by
  unfold boundaryPolynomial
  rw [natDegree_C_mul (inv_ne_zero (ne_of_gt (normalizer_pos r n)))]
  have hl : ((ascPochhammer ℝ r).comp (X + 1)).natDegree ≤ r := by
    have hlin : (X + 1 : ℝ[X]).natDegree = 1 := by
      simpa using natDegree_X_add_C (1 : ℝ)
    exact natDegree_comp_le.trans (by rw [ascPochhammer_natDegree, hlin, mul_one])
  have hr : ((ascPochhammer ℝ (r + 1)).comp (C (n : ℝ) - X)).natDegree ≤ r + 1 := by
    have hlin : (C (n : ℝ) - X).natDegree = 1 := by
      rw [show C (n : ℝ) - X = -(X - C (n : ℝ)) by ring, natDegree_neg, natDegree_X_sub_C]
    exact natDegree_comp_le.trans (by rw [ascPochhammer_natDegree, hlin, mul_one])
  have hh := natDegree_mul_le
    (p := (ascPochhammer ℝ r).comp (X + 1))
    (q := (ascPochhammer ℝ (r + 1)).comp (C (n : ℝ) - X))
  omega

theorem left_ghost_zero (r n k : ℕ) (hk : k < r) :
    value r n (-(k + 1 : ℝ)) = 0 := by
  rw [value_formula]
  rw [show -(k + 1 : ℝ) + 1 = -(k : ℝ) by ring,
    ascPochhammer_eval_neg_coe_nat_of_lt hk]
  ring

theorem right_ghost_zero (r n k : ℕ) (hk : k ≤ r) :
    value r n ((n : ℝ) + k) = 0 := by
  rw [value_formula]
  rw [show (n : ℝ) - ((n : ℝ) + k) = -(k : ℝ) by ring,
    ascPochhammer_eval_neg_coe_nat_of_lt (Nat.lt_succ_of_le hk)]
  ring

theorem extreme_left_value (r n : ℕ) :
    value r n (-(r + 1 : ℝ)) = (-1 : ℝ) ^ r := by
  rw [value_formula]
  rw [show -(r + 1 : ℝ) + 1 = -(r : ℝ) by ring,
    ascPochhammer_eval_neg_eq_descPochhammer,
    descPochhammer_eval_eq_descFactorial, Nat.descFactorial_self]
  rw [show (n : ℝ) - -(r + 1 : ℝ) = (n : ℝ) + (r + 1) by ring]
  have hn := ne_of_gt (normalizer_pos r n)
  unfold normalizer at *
  field_simp [(mul_ne_zero_iff.mp hn).2]

/-- The exact central recurrence before imposing the zero ghost values. -/
theorem full_recurrence (r n : ℕ) (x : ℝ) :
    ∑ l ∈ Finset.range (2 * (r + 1) + 1),
      ((-1 : ℝ) ^ (2 * (r + 1) - l) * ((2 * (r + 1)).choose l : ℝ)) *
        value r n (x + l) = 0 := by
  have H := congr_fun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt
    (boundaryPolynomial_degree r n)) x
  rw [fwdDiff_iter_eq_sum_shift] at H
  simpa only [Pi.zero_apply, zsmul_eq_mul, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Int.cast_natCast, nsmul_eq_mul, mul_one, value] using H

/-- Centered signed-binomial coefficient, indexed from 0 through 2m. -/
def central (m l : ℕ) : ℝ := (-1 : ℝ) ^ (m + l) * ((2 * m).choose l : ℝ)

theorem coefficient_central (m i j : ℕ) (h : i ≤ m + j) :
    MF21Challenge.coefficient m (Nat.dist i j) = central m (m + j - i) := by
  unfold MF21Challenge.coefficient central
  rcases le_total i j with hij | hji
  · rw [Nat.dist_eq_sub_of_le hij,
      show m + j - i = m + (j - i) by omega]
    congr 1
    rw [show m + (m + (j - i)) = 2 * m + (j - i) by omega, pow_add, pow_mul]
    norm_num
  · rw [Nat.dist_eq_sub_of_le_right hji]
    have hchoose : (2 * m).choose (m + (i - j)) =
        (2 * m).choose (m + j - i) := by
      rw [← Nat.choose_symm (by omega : m + (i - j) ≤ 2 * m)]
      congr 1
      omega
    rw [hchoose]
    congr 1
    rw [show m + (m + j - i) = 2 * (m + j - i) + (i - j) by omega,
      pow_add, pow_mul]
    norm_num

theorem coefficient_nonzero_band (m i j : ℕ)
    (h : MF21Challenge.coefficient m (Nat.dist i j) ≠ 0) :
    i ≤ m + j ∧ j ≤ m + i := by
  have hd : Nat.dist i j ≤ m := by
    by_contra hbad
    have hz : (2 * m).choose (m + Nat.dist i j) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    simp [MF21Challenge.coefficient, hz] at h
  unfold Nat.dist at hd
  omega

def padded (m n : ℕ) (u : ℕ → ℝ) (k : ℕ) : ℝ :=
  if m ≤ k ∧ k < m + n then u (k - m) else 0

theorem row_term_eq (m n i j : ℕ) (u : ℕ → ℝ)
    (hj : j < n) (hlo : i ≤ m + j) :
    MF21Challenge.coefficient m (Nat.dist i j) * u j =
      central m (m + j - i) * padded m n u (i + (m + j - i)) := by
  rw [coefficient_central m i j hlo]
  have hk : i + (m + j - i) = m + j := by omega
  simp [padded, hk, hj]

/-- Exact finite reindexing of the Toeplitz row as a centered difference.
Zero coefficients outside the bandwidth are included on either side. -/
theorem row_convolution (m n i : ℕ) (u : ℕ → ℝ) :
    (∑ j ∈ Finset.range n, MF21Challenge.coefficient m (Nat.dist i j) * u j) =
      ∑ l ∈ Finset.range (2 * m + 1), central m l * padded m n u (i + l) := by
  apply Finset.sum_bij_ne_zero (fun j _ _ ↦ m + j - i)
  · intro j hj hne
    have hb := coefficient_nonzero_band m i j (left_ne_zero_of_mul hne)
    exact Finset.mem_range.mpr (by omega)
  · intro j hj hjne k hk hkne heq
    have hjb := coefficient_nonzero_band m i j (left_ne_zero_of_mul hjne)
    have hkb := coefficient_nonzero_band m i k (left_ne_zero_of_mul hkne)
    omega
  · intro l hl hlne
    have hins : m ≤ i + l ∧ i + l < m + n := by
      by_contra hbad
      simp [padded, hbad] at hlne
    have hj : i + l - m < n := by omega
    have hlo : i ≤ m + (i + l - m) := by omega
    have hmap : m + (i + l - m) - i = l := by omega
    have heq := row_term_eq m n i (i + l - m) u hj hlo
    rw [hmap] at heq
    exact ⟨i + l - m, Finset.mem_range.mpr hj, heq.trans_ne hlne, hmap⟩
  · intro j hj hne
    have hb := coefficient_nonzero_band m i j (left_ne_zero_of_mul hne)
    exact row_term_eq m n i j u (Finset.mem_range.mp hj) hb.1

/-- Central recurrence with the sign convention of the matrix coefficients. -/
theorem central_recurrence (r n : ℕ) (x : ℝ) :
    ∑ l ∈ Finset.range (2 * (r + 1) + 1),
      central (r + 1) l * value r n (x + l) = 0 := by
  have H := congrArg (fun z : ℝ ↦ (-1) ^ (r + 1) * z) (full_recurrence r n x)
  rw [mul_zero, Finset.mul_sum] at H
  convert H using 1
  apply Finset.sum_congr rfl
  intro l hl
  have hl' : l ≤ 2 * (r + 1) := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
  have hs : (-1 : ℝ) ^ (2 * (r + 1) - l) = (-1 : ℝ) ^ l := by
    calc
      (-1 : ℝ) ^ (2 * (r + 1) - l) =
          (-1 : ℝ) ^ ((2 * (r + 1) - l) % 2) := neg_one_pow_eq_pow_mod_two _
      _ = (-1 : ℝ) ^ (l % 2) := by congr 1; omega
      _ = (-1 : ℝ) ^ l := (neg_one_pow_eq_pow_mod_two _).symm
  simp only [central, hs, pow_add]
  ring

/-- The only nonzero omitted ghost value is the extreme left value. -/
theorem value_eq_padded_add_ghost (r n k : ℕ) (hk : k < n + 2 * (r + 1)) :
    value r n ((k : ℝ) - (r + 1)) =
      padded (r + 1) n (fun j ↦ value r n (j : ℝ)) k +
        if k = 0 then (-1 : ℝ) ^ r else 0 := by
  by_cases hk0 : k = 0
  · subst k
    simp only [Nat.cast_zero, zero_sub]
    rw [extreme_left_value]
    simp [padded]
  rw [if_neg hk0]
  by_cases hl : r + 1 ≤ k
  · by_cases hr : k < r + 1 + n
    · simp [padded, hl, hr, Nat.cast_sub hl]
    · have hnk : n ≤ k - (r + 1) := by omega
      have hq : k - (r + 1) - n ≤ r := by omega
      have hz := right_ghost_zero r n (k - (r + 1) - n) hq
      have heq : (n : ℝ) + ((k - (r + 1) - n : ℕ) : ℝ) =
          (k : ℝ) - (r + 1) := by
        rw [Nat.cast_sub hnk, Nat.cast_sub hl]
        push_cast
        ring
      rw [heq] at hz
      simp [padded, hr, hz]
  · have hkr : k ≤ r := by omega
    have hq : r - k < r := by omega
    have hz := left_ghost_zero r n (r - k) hq
    have heq : -(((r - k : ℕ) : ℝ) + 1) = (k : ℝ) - (r + 1) := by
      rw [Nat.cast_sub hkr]
      ring
    rw [heq] at hz
    simp [padded, hl, hz]

theorem central_extreme_sign (r : ℕ) :
    central (r + 1) 0 * (-1 : ℝ) ^ r = -1 := by
  simp only [central, add_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
  rw [← pow_add, show r + 1 + r = 2 * r + 1 by omega, pow_add, pow_mul]
  norm_num

/-- The candidate first column solves the exact finite matrix equation. -/
theorem row_sum_first_column (r n i : ℕ) (hi : i < n) :
    (∑ j ∈ Finset.range n,
      MF21Challenge.coefficient (r + 1) (Nat.dist i j) * value r n (j : ℝ)) =
        if i = 0 then 1 else 0 := by
  rw [row_convolution]
  have H := central_recurrence r n ((i : ℝ) - (r + 1))
  have heach (l : ℕ) (hl : l ∈ Finset.range (2 * (r + 1) + 1)) :
      central (r + 1) l * value r n ((i : ℝ) - (r + 1) + l) =
        central (r + 1) l *
          padded (r + 1) n (fun j ↦ value r n (j : ℝ)) (i + l) +
            if i = 0 ∧ l = 0 then (-1 : ℝ) else 0 := by
    have hln : l ≤ 2 * (r + 1) := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
    have hbound : i + l < n + 2 * (r + 1) := by omega
    rw [show (i : ℝ) - (r + 1) + l = ((i + l : ℕ) : ℝ) - (r + 1) by push_cast; ring]
    rw [value_eq_padded_add_ghost r n (i + l) hbound, mul_add]
    by_cases hii : i = 0
    · subst i
      by_cases hll : l = 0
      · subst l
        simp [central_extreme_sign]
      · simp [hll]
    · simp [hii]
  rw [Finset.sum_congr rfl heach, Finset.sum_add_distrib] at H
  by_cases hi0 : i = 0
  · simp [hi0] at H ⊢
    linarith
  · simpa [hi0] using H

def firstColumn (r n : ℕ) : Fin n → ℝ := fun j ↦ value r n (j.val : ℝ)

/-- Unconditional matrix form of the exact first-column equation for m=r+1.
No inverse formula, limiting theorem, or numerical premise is assumed. -/
theorem toeplitz_mulVec_firstColumn (r n : ℕ) :
    (MF21Challenge.toeplitz (r + 1) n).mulVec (firstColumn r n) =
      fun i : Fin n ↦ if i.val = 0 then 1 else 0 := by
  funext i
  dsimp [Matrix.mulVec, dotProduct, MF21Challenge.toeplitz, firstColumn]
  exact (Fin.sum_univ_eq_sum_range (fun j : ℕ ↦
    MF21Challenge.coefficient (r + 1) (Nat.dist i.val j) * value r n (j : ℝ)) n).trans
      (row_sum_first_column r n i.val i.isLt)

/-- Closed rational formula for the candidate first column, m=r+1. -/
theorem value_nat_closed (r n j : ℕ) (hj : j ≤ n) :
    value r n (j : ℝ) =
      (((r + j).choose j : ℕ) : ℝ) * ((n - j).ascFactorial (r + 1) : ℝ) /
        ((n + r + 1).ascFactorial (r + 1) : ℝ) := by
  rw [value_formula]
  have hleft : (ascPochhammer ℝ r).eval ((j : ℝ) + 1) =
      (r.factorial : ℝ) * ((r + j).choose j : ℝ) := by
    rw [← Nat.cast_add_one, ascPochhammer_nat_eq_natCast_ascFactorial,
      Nat.ascFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    congr 1
    rw [← Nat.choose_symm (by omega : r ≤ j + r)]
    rw [show j + r - r = j by omega, Nat.add_comm j r]
  have hright : (ascPochhammer ℝ (r + 1)).eval ((n : ℝ) - j) =
      ((n - j).ascFactorial (r + 1) : ℝ) := by
    rw [← Nat.cast_sub hj, ascPochhammer_nat_eq_natCast_ascFactorial]
  have hnorm : normalizer r n = (r.factorial : ℝ) *
      ((n + r + 1).ascFactorial (r + 1) : ℝ) := by
    unfold normalizer
    congr 1
    rw [show (n : ℝ) + (r + 1) = ((n + r + 1 : ℕ) : ℝ) by push_cast; ring]
    exact ascPochhammer_nat_eq_natCast_ascFactorial ℝ _ _
  rw [hleft, hright, hnorm]
  have hf : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  field_simp

/-- Closed form of the exact solution of A u=e_0. -/
theorem firstColumn_closed (r n : ℕ) (j : Fin n) :
    firstColumn r n j =
      (((r + j.val).choose j.val : ℕ) : ℝ) *
        ((n - j.val).ascFactorial (r + 1) : ℝ) /
        ((n + r + 1).ascFactorial (r + 1) : ℝ) :=
  value_nat_closed r n j.val (Nat.le_of_lt j.isLt)

/-- The polynomial solution is the actual first inverse column. Invertibility
is proved for this matrix family by its difference-Gram representation. -/
theorem inverse_column_eq (r n : ℕ) (j : Fin (n + 1)) :
    ((MF21Challenge.toeplitz (r + 1) (n + 1))⁻¹) j 0 =
      firstColumn r (n + 1) j := by
  let A := MF21Challenge.toeplitz (r + 1) (n + 1)
  have hdet : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).mp (MF21Challenge.toeplitz_posDef _ _).isUnit
  have H := congrArg (Matrix.mulVec A⁻¹) (toeplitz_mulVec_firstColumn r (n + 1))
  have he0 : (fun i : Fin (n + 1) ↦ if i.val = 0 then (1 : ℝ) else 0) =
      Pi.single 0 1 := by
    funext i
    by_cases hi : i = 0
    · subst i
      simp
    · have hv : i.val ≠ 0 := fun hv ↦ hi (Fin.ext hv)
      simp [hi, hv]
  change A⁻¹ *ᵥ (A *ᵥ firstColumn r (n + 1)) = _ at H
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hdet, Matrix.one_mulVec,
    he0, Matrix.mulVec_single_one] at H
  exact (congrFun H j).symm

/-- Exact binomial/rising-factorial formula for the actual inverse entries. -/
theorem inverse_column_closed (r n : ℕ) (j : Fin (n + 1)) :
    ((MF21Challenge.toeplitz (r + 1) (n + 1))⁻¹) j 0 =
      (((r + j.val).choose j.val : ℕ) : ℝ) *
        ((n + 1 - j.val).ascFactorial (r + 1) : ℝ) /
        ((n + 1 + r + 1).ascFactorial (r + 1) : ℝ) := by
  rw [inverse_column_eq, firstColumn_closed]

end MF21FirstColumn

#print axioms MF21FirstColumn.full_recurrence
#print axioms MF21FirstColumn.extreme_left_value

#print axioms MF21FirstColumn.row_convolution

#print axioms MF21FirstColumn.toeplitz_mulVec_firstColumn

#print axioms MF21FirstColumn.firstColumn_closed

#print axioms MF21FirstColumn.inverse_column_closed
