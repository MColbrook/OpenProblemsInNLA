import MF21.Definitions
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

/-! The finite difference Gram factorization of the explicit MF-21 matrix.
This module addresses the actual matrix from Challenge, not an abstract spectrum.
-/

open scoped BigOperators
open Finset Matrix
noncomputable section
namespace MF21Challenge

theorem choose_shift_convolution (m d : ℕ) :
    ∑ t ∈ Finset.range (m + 1), m.choose (t + d) * m.choose t =
      (2 * m).choose (m + d) := by
  have hv := Nat.add_choose_eq m m (m + d)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hv
  have htrunc :
      ∑ k ∈ range (m + d + 1), m.choose k * m.choose (m + d - k) =
      ∑ k ∈ range (m + 1), m.choose k * m.choose (m + d - k) := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro k hk hnot
    have hmk : m < k := by simpa using hnot
    simp [Nat.choose_eq_zero_of_lt hmk]
  rw [htrunc] at hv
  have hr := Finset.sum_range_reflect
    (fun k => m.choose k * m.choose (m + d - k)) (m + 1)
  calc
    _ = ∑ k ∈ range (m + 1), m.choose (m - k) *
        m.choose (m + d - (m - k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ m := by simpa using hk
      rw [Nat.choose_symm hk', show m + d - (m - k) = k + d by omega,
        Nat.mul_comm]
    _ = ∑ k ∈ range (m + 1), m.choose k * m.choose (m + d - k) := by
      simpa using hr
    _ = (2 * m).choose (m + d) := by simpa [two_mul] using hv.symm

def unsignedDifferenceEntry (m row col : ℕ) : ℝ :=
  if col ≤ row then (m.choose (row - col) : ℝ) else 0

def differenceEntry (m row col : ℕ) : ℝ :=
  (-1 : ℝ) ^ (row + col) * unsignedDifferenceEntry m row col

def differenceMatrix (m n : ℕ) : Matrix (Fin (n + m)) (Fin n) ℝ :=
  fun row col => differenceEntry m row.val col.val

theorem unsigned_difference_correlation (m n i j : ℕ)
    (_hi : i < n) (hj : j < n) (hij : i ≤ j) :
    ∑ k ∈ range (n + m),
      unsignedDifferenceEntry m k i * unsignedDifferenceEntry m k j =
      ((2 * m).choose (m + (j - i)) : ℝ) := by
  rw [show n + m = j + (n + m - j) by omega, Finset.sum_range_add]
  have hzero : ∑ k ∈ range j,
      unsignedDifferenceEntry m k i * unsignedDifferenceEntry m k j = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp only [Finset.mem_range] at hk
    simp [unsignedDifferenceEntry, show ¬ j ≤ k by omega]
  rw [hzero, zero_add]
  have hshift : ∑ k ∈ range (n + m - j),
      unsignedDifferenceEntry m (j + k) i * unsignedDifferenceEntry m (j + k) j =
      ∑ k ∈ range (n + m - j),
        (m.choose (k + (j - i)) : ℝ) * (m.choose k : ℝ) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp [unsignedDifferenceEntry, show i ≤ j + k by omega,
      show j ≤ j + k by omega, show j + k - i = k + (j - i) by omega]
  rw [hshift]
  have htrunc :
      ∑ k ∈ range (n + m - j),
        (m.choose (k + (j - i)) : ℝ) * (m.choose k : ℝ) =
      ∑ k ∈ range (m + 1),
        (m.choose (k + (j - i)) : ℝ) * (m.choose k : ℝ) := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro k hk hnot
    have hmk : m < k := by simpa using hnot
    simp [Nat.choose_eq_zero_of_lt hmk]
  rw [htrunc]
  exact_mod_cast choose_shift_convolution m (j - i)

theorem sign_pair (row i j : ℕ) (hij : i ≤ j) :
    (-1 : ℝ) ^ (row + i) * (-1 : ℝ) ^ (row + j) =
      (-1 : ℝ) ^ (j - i) := by
  rw [← pow_add, show (row + i) + (row + j) = 2 * (row + i) + (j - i) by omega,
    pow_add, pow_mul]
  norm_num

theorem difference_correlation (m n i j : ℕ)
    (hi : i < n) (hj : j < n) (hij : i ≤ j) :
    ∑ k ∈ range (n + m), differenceEntry m k i * differenceEntry m k j =
      coefficient m (j - i) := by
  calc
    _ = ∑ k ∈ range (n + m), (-1 : ℝ) ^ (j - i) *
        (unsignedDifferenceEntry m k i * unsignedDifferenceEntry m k j) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [differenceEntry]
      calc
        _ = ((-1 : ℝ) ^ (k + i) * (-1 : ℝ) ^ (k + j)) *
          (unsignedDifferenceEntry m k i * unsignedDifferenceEntry m k j) := by ring
        _ = _ := by rw [sign_pair k i j hij]
    _ = _ := by
      rw [← Finset.mul_sum, unsigned_difference_correlation m n i j hi hj hij]
      rfl

/-- The explicit Toeplitz matrix is the Gram matrix of the finite difference
map with zero extension at both ends. -/
theorem toeplitz_eq_difference_gram (m n : ℕ) :
    toeplitz m n = (differenceMatrix m n)ᴴ * differenceMatrix m n := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, differenceMatrix, star_trivial]
  change coefficient m (Nat.dist i.val j.val) =
    ∑ k : Fin (n + m), (fun r : ℕ => differenceEntry m r i.val *
      differenceEntry m r j.val) k.val
  rw [Fin.sum_univ_eq_sum_range
    (fun r : ℕ => differenceEntry m r i.val * differenceEntry m r j.val) (n + m)]
  rcases le_total i.val j.val with hij | hji
  · simpa only [toeplitz, Nat.dist_eq_sub_of_le hij] using
      (difference_correlation m n i.val j.val i.isLt j.isLt hij).symm
  · rw [show (∑ k ∈ range (n + m), differenceEntry m k i.val * differenceEntry m k j.val) =
        ∑ k ∈ range (n + m), differenceEntry m k j.val * differenceEntry m k i.val by
          apply Finset.sum_congr rfl
          intro k hk
          ring]
    simpa only [toeplitz, Nat.dist_eq_sub_of_le_right hji] using
      (difference_correlation m n j.val i.val j.isLt i.isLt hji).symm

@[simp] theorem differenceEntry_diagonal (m i : ℕ) :
    differenceEntry m i i = 1 := by
  simp only [differenceEntry, unsignedDifferenceEntry, le_refl, if_true, Nat.sub_self,
    Nat.choose_zero_right, Nat.cast_one, mul_one]
  rw [show i + i = 2 * i by omega, pow_mul]
  norm_num

theorem differenceEntry_of_lt (m row col : ℕ) (h : row < col) :
    differenceEntry m row col = 0 := by
  simp [differenceEntry, unsignedDifferenceEntry, show ¬ col ≤ row by omega]

theorem differenceMatrix_mulVec_eq_zero (m n : ℕ) (x : Fin n → ℝ)
    (hx : differenceMatrix m n *ᵥ x = 0) : x = 0 := by
  have hval : ∀ k : ℕ, ∀ hk : k < n, x ⟨k, hk⟩ = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      have hr := congrFun hx (⟨k, by omega⟩ : Fin (n + m))
      change (∑ b : Fin n, differenceEntry m k b.val * x b) = 0 at hr
      have hsum : (∑ b : Fin n, differenceEntry m k b.val * x b) = x ⟨k, hk⟩ := by
        rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin n)]
        · simp
        · intro b hb hne
          by_cases hbk : b.val < k
          · have hz : x b = 0 := ih b.val hbk b.isLt
            simp [hz]
          · have hbne : b.val ≠ k := fun h => hne (Fin.ext h)
            rw [differenceEntry_of_lt m k b.val (by omega), zero_mul]
        · simp
      rwa [hsum] at hr
  funext j
  exact hval j.val j.isLt

theorem differenceMatrix_injective (m n : ℕ) :
    Function.Injective (differenceMatrix m n).mulVec := by
  intro x y h
  apply sub_eq_zero.mp
  apply differenceMatrix_mulVec_eq_zero m n
  rw [Matrix.mulVec_sub, h, sub_self]

/-- Positive definiteness of the actual signed-binomial Toeplitz matrix. -/
theorem toeplitz_posDef (m n : ℕ) : (toeplitz m n).PosDef := by
  rw [toeplitz_eq_difference_gram]
  exact Matrix.PosDef.conjTranspose_mul_self _ (differenceMatrix_injective m n)

/-- Every actual eigenvalue used in the MF-21 target is strictly positive. -/
theorem eigenvalue_pos (m n : ℕ) (j : Fin n) : 0 < eigenvalue m n j := by
  have hpos := (toeplitz_isHermitian m n).posDef_iff_eigenvalues_pos.mp
    (toeplitz_posDef m n)
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
  have h0 : ∀ k : Fin (Fintype.card (Fin n)),
      0 < (toeplitz_isHermitian m n).eigenvalues₀ k := by
    intro k
    simpa only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply] using hpos (e k)
  exact h0 _

/-- In particular the inverse matrix used in the trace argument exists. -/
theorem toeplitz_det_pos (m n : ℕ) : 0 < (toeplitz m n).det :=
  (toeplitz_posDef m n).det_pos

end MF21Challenge

#print axioms MF21Challenge.choose_shift_convolution
#print axioms MF21Challenge.unsigned_difference_correlation
#print axioms MF21Challenge.difference_correlation
#print axioms MF21Challenge.toeplitz_eq_difference_gram
#print axioms MF21Challenge.differenceMatrix_mulVec_eq_zero
#print axioms MF21Challenge.differenceMatrix_injective
#print axioms MF21Challenge.toeplitz_posDef
#print axioms MF21Challenge.eigenvalue_pos
#print axioms MF21Challenge.toeplitz_det_pos
