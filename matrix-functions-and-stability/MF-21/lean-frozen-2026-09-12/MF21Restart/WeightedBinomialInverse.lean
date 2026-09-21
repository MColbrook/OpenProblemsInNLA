import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
A division-free telescoping proof of the weighted binomial identity behind
the known Duduchava–Roch inverse formula. This module proves a finite
identity, not a matrix inverse formula or a uniform inverse-kernel limit.
The statement/proof lock is `WEIGHTED_BINOMIAL_INVERSE_STATEMENTS.md`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

def weightedBinomialRisingSum (m d : ℕ) (x : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (m - d + 1),
    (m.choose r : ℝ) * (m.choose (d + r) : ℝ) *
      (ascPochhammer ℝ (2 * m)).eval (x - (r : ℝ))

private def weightedBinomialWeight (m d r : ℕ) : ℝ :=
  (m.choose r : ℝ) * (m.choose (d + r) : ℝ)

private theorem rising_shift_identity (a : ℕ) (x : ℝ) :
    x * (ascPochhammer ℝ a).eval (x + 1) =
      (x + (a : ℝ)) * (ascPochhammer ℝ a).eval x := by
  calc
    x * (ascPochhammer ℝ a).eval (x + 1) =
        (ascPochhammer ℝ (a + 1)).eval x := by
      rw [ascPochhammer_succ_left]
      simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
        Polynomial.eval_add, Polynomial.eval_one]
    _ = (ascPochhammer ℝ a).eval x * (x + (a : ℝ)) := ascPochhammer_succ_eval a x
    _ = _ := mul_comm _ _

private theorem weightedBinomialWeight_shift (m d r : ℕ) (hd : d ≤ m)
    (hr : r ≤ m - d) :
    ((r : ℝ) + 1) * ((d : ℝ) + r + 1) * weightedBinomialWeight m d (r + 1) =
      ((m : ℝ) - r) * ((m : ℝ) - d - r) * weightedBinomialWeight m d r := by
  have hrm : r ≤ m := by omega
  have hdr : d + r ≤ m := by omega
  have h₁ : (m.choose (r + 1) : ℝ) * ((r : ℝ) + 1) =
      (m.choose r : ℝ) * ((m : ℝ) - r) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hrm] using
      congrArg (fun t : ℕ => (t : ℝ)) (Nat.choose_succ_right_eq m r)
  have h₂ : (m.choose (d + (r + 1)) : ℝ) * ((d : ℝ) + r + 1) =
      (m.choose (d + r) : ℝ) * ((m : ℝ) - ((d : ℝ) + r)) := by
    simpa only [Nat.add_assoc, add_assoc, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_sub hdr] using
      congrArg (fun t : ℕ => (t : ℝ)) (Nat.choose_succ_right_eq m (d + r))
  unfold weightedBinomialWeight
  calc
    ((r : ℝ) + 1) * ((d : ℝ) + r + 1) *
        ((m.choose (r + 1) : ℝ) * (m.choose (d + (r + 1)) : ℝ)) =
        ((m.choose (r + 1) : ℝ) * ((r : ℝ) + 1)) *
          ((m.choose (d + (r + 1)) : ℝ) * ((d : ℝ) + r + 1)) := by ring
    _ = ((m.choose r : ℝ) * ((m : ℝ) - r)) *
        ((m.choose (d + r) : ℝ) * ((m : ℝ) - ((d : ℝ) + r))) := by rw [h₁, h₂]
    _ = _ := by ring

/-- The recurrence is a polynomial identity: no division by x or x-r is used. -/
theorem weightedBinomialRisingSum_recurrence (m d : ℕ) (hd : d ≤ m) (x : ℝ) :
    x * (x + (d : ℝ)) * weightedBinomialRisingSum m d (x + 1) =
      (x + (m : ℝ)) * (x + (m : ℝ) + d) * weightedBinomialRisingSum m d x := by
  let P : ℝ → ℝ := fun y => (ascPochhammer ℝ (2 * m)).eval y
  let w : ℕ → ℝ := weightedBinomialWeight m d
  let G : ℕ → ℝ := fun r => -((r : ℝ) * ((d : ℝ) + r) * w r * P (x + 1 - r))
  have hstep (r : ℕ) (hr : r ∈ Finset.range (m - d + 1)) :
      x * (x + (d : ℝ)) * (w r * P (x + 1 - r)) -
        (x + (m : ℝ)) * (x + (m : ℝ) + d) * (w r * P (x - r)) =
        G (r + 1) - G r := by
    have hrle : r ≤ m - d := by have := Finset.mem_range.mp hr; omega
    have hw := weightedBinomialWeight_shift m d r hd hrle
    change ((r : ℝ) + 1) * ((d : ℝ) + r + 1) * w (r + 1) =
      ((m : ℝ) - r) * ((m : ℝ) - d - r) * w r at hw
    have hp := rising_shift_identity (2 * m) (x - (r : ℝ))
    rw [show x - (r : ℝ) + 1 = x + 1 - r by ring] at hp
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hp
    change (x - (r : ℝ)) * P (x + 1 - r) =
      (x - r + 2 * (m : ℝ)) * P (x - r) at hp
    dsimp only [G]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show x + 1 - ((r : ℝ) + 1) = x - r by ring]
    linear_combination (x + (r : ℝ) + d) * w r * hp + P (x - r) * hw
  have hGzero : G 0 = 0 := by simp [G]
  have hGlast : G (m - d + 1) = 0 := by
    have hz : m.choose (d + (m - d + 1)) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    simp [G, w, weightedBinomialWeight, hz]
  apply sub_eq_zero.mp
  calc
    x * (x + (d : ℝ)) * weightedBinomialRisingSum m d (x + 1) -
        (x + (m : ℝ)) * (x + (m : ℝ) + d) * weightedBinomialRisingSum m d x =
        ∑ r ∈ Finset.range (m - d + 1),
          (x * (x + (d : ℝ)) * (w r * P (x + 1 - r)) -
            (x + (m : ℝ)) * (x + (m : ℝ) + d) * (w r * P (x - r))) := by
      dsimp only [weightedBinomialRisingSum, w, weightedBinomialWeight, P]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    _ = ∑ r ∈ Finset.range (m - d + 1), (G (r + 1) - G r) :=
      Finset.sum_congr rfl hstep
    _ = G (m - d + 1) - G 0 := Finset.sum_range_sub G (m - d + 1)
    _ = 0 := by rw [hGlast, hGzero, sub_self]

private theorem weightedBinomialRisingSum_one (m d : ℕ) (hm : 1 ≤ m) :
    weightedBinomialRisingSum m d 1 = (m.choose d : ℝ) * ((2 * m).factorial : ℝ) := by
  unfold weightedBinomialRisingSum
  rw [Finset.sum_eq_single 0]
  · simp only [Nat.choose_zero_right, Nat.cast_one, Nat.add_zero, Nat.cast_zero,
      one_mul, sub_zero, ascPochhammer_eval_one]
  · intro r hr hne
    have hrle : r ≤ m - d := by have := Finset.mem_range.mp hr; omega
    have hrpos : 1 ≤ r := by omega
    have hroot : r - 1 < 2 * m := by omega
    have hx : (1 : ℝ) - (r : ℝ) = -((r - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hrpos, Nat.cast_one]
      ring
    rw [hx, ascPochhammer_eval_neg_coe_nat_of_lt hroot, mul_zero]
  · simp

private theorem weightedBinomial_initial_value (m d : ℕ) (hm : 1 ≤ m) (hd : d ≤ m) :
    weightedBinomialRisingSum m d 1 =
      ((2 * m).choose (m + d) : ℝ) * (ascPochhammer ℝ m).eval 1 *
        (ascPochhammer ℝ m).eval (1 + (d : ℝ)) := by
  have hfact (a : ℕ) : (a.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)
  have heval : (ascPochhammer ℝ m).eval ((d : ℝ) + 1) =
      ((d + m).factorial : ℝ) / (d.factorial : ℝ) := by
    apply (eq_div_iff (hfact d)).mpr
    simpa only [mul_comm] using factorial_mul_ascPochhammer ℝ d m
  rw [weightedBinomialRisingSum_one m d hm, ascPochhammer_eval_one,
    show (1 : ℝ) + d = (d : ℝ) + 1 by ring, heval,
    Nat.cast_choose ℝ hd, Nat.cast_choose ℝ (show m + d ≤ 2 * m by omega),
    show 2 * m - (m + d) = m - d by omega, Nat.add_comm d m]
  field_simp [hfact]

private theorem weightedBinomialRisingSum_nat_add_one (m d : ℕ)
    (hm : 1 ≤ m) (hd : d ≤ m) (j : ℕ) :
    weightedBinomialRisingSum m d ((j : ℝ) + 1) =
      ((2 * m).choose (m + d) : ℝ) *
        (ascPochhammer ℝ m).eval ((j : ℝ) + 1) *
        (ascPochhammer ℝ m).eval ((j : ℝ) + 1 + d) := by
  induction j with
  | zero => simpa only [Nat.cast_zero, zero_add] using weightedBinomial_initial_value m d hm hd
  | succ j ih =>
    let x : ℝ := (j : ℝ) + 1
    let P : ℝ → ℝ := fun y => (ascPochhammer ℝ m).eval y
    let C : ℝ := ((2 * m).choose (m + d) : ℝ)
    have hden : x * (x + (d : ℝ)) ≠ 0 := by dsimp [x]; positivity
    simp only [Nat.cast_succ, Nat.cast_add, Nat.cast_one]
    change weightedBinomialRisingSum m d (x + 1) = C * P (x + 1) * P (x + 1 + d)
    apply mul_left_cancel₀ hden
    rw [weightedBinomialRisingSum_recurrence m d hd x]
    have hix : weightedBinomialRisingSum m d x = C * P x * P (x + d) := ih
    rw [hix]
    have h₁ := rising_shift_identity m x
    have h₂ := rising_shift_identity m (x + (d : ℝ))
    rw [show x + (d : ℝ) + 1 = x + 1 + d by ring] at h₂
    change x * P (x + 1) = (x + (m : ℝ)) * P x at h₁
    change (x + (d : ℝ)) * P (x + 1 + d) = (x + d + (m : ℝ)) * P (x + d) at h₂
    calc
      (x + (m : ℝ)) * (x + (m : ℝ) + d) * (C * P x * P (x + d)) =
          C * ((x + (m : ℝ)) * P x) * ((x + d + (m : ℝ)) * P (x + d)) := by ring
      _ = C * (x * P (x + 1)) * ((x + (d : ℝ)) * P (x + 1 + d)) := by rw [← h₁, ← h₂]
      _ = x * (x + (d : ℝ)) * (C * P (x + 1) * P (x + 1 + d)) := by ring

/-- The real polynomial identity underlying the finite inverse factorization. -/
theorem weightedBinomialRisingSum_eq (m d : ℕ)
    (hm : 1 ≤ m) (hd : d ≤ m) (x : ℝ) :
    weightedBinomialRisingSum m d x =
      ((2 * m).choose (m + d) : ℝ) *
        (ascPochhammer ℝ m).eval x *
        (ascPochhammer ℝ m).eval (x + (d : ℝ)) := by
  let p : Polynomial ℝ := ∑ r ∈ Finset.range (m - d + 1),
    Polynomial.C ((m.choose r : ℝ) * (m.choose (d + r) : ℝ)) *
      (ascPochhammer ℝ (2 * m)).comp (Polynomial.X - Polynomial.C (r : ℝ))
  let q : Polynomial ℝ := Polynomial.C ((2 * m).choose (m + d) : ℝ) *
    ascPochhammer ℝ m * (ascPochhammer ℝ m).comp (Polynomial.X + Polynomial.C (d : ℝ))
  have hp (y : ℝ) : p.eval y = weightedBinomialRisingSum m d y := by
    simp only [p, weightedBinomialRisingSum, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X]
  have hq (y : ℝ) : q.eval y = ((2 * m).choose (m + d) : ℝ) *
      (ascPochhammer ℝ m).eval y * (ascPochhammer ℝ m).eval (y + (d : ℝ)) := by
    simp only [q, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_X]
  have hinj : Function.Injective (fun j : ℕ => (j : ℝ) + 1) := by
    intro a b hab
    exact Nat.cast_injective (add_right_cancel hab)
  have heq : p = q := Polynomial.eq_of_infinite_eval_eq p q
    ((Set.infinite_range_of_injective hinj).mono (by
      rintro y ⟨j, rfl⟩
      change p.eval ((j : ℝ) + 1) = q.eval ((j : ℝ) + 1)
      rw [hp, hq]
      exact weightedBinomialRisingSum_nat_add_one m d hm hd j))
  simpa only [hp, hq] using congrArg (Polynomial.eval x) heq

/-- The exact one-based weighted sum, including the identically zero case d>m.
Here i=j+d, so every natural subtraction in a binomial index is in range. -/
theorem weightedBinomialInverse_identity (m d j : ℕ)
    (hm : 1 ≤ m) (hj : 1 ≤ j) :
    (∑ k ∈ Finset.Icc 1 j,
      (m.choose (j + d - k) : ℝ) * (m.choose (j - k) : ℝ) *
        (k.ascFactorial (2 * m) : ℝ)) =
      (j.ascFactorial m : ℝ) * ((j + d).ascFactorial m : ℝ) *
        ((2 * m).choose (m + d) : ℝ) := by
  by_cases hd : d ≤ m
  · let P : ℝ → ℝ := fun x => (ascPochhammer ℝ (2 * m)).eval x
    let w : ℕ → ℝ := weightedBinomialWeight m d
    let f : ℕ → ℝ := fun r => w r * P ((j : ℝ) - r)
    have hreverse :
        (∑ k ∈ Finset.Icc 1 j,
          (m.choose (j + d - k) : ℝ) * (m.choose (j - k) : ℝ) *
            (k.ascFactorial (2 * m) : ℝ)) = ∑ r ∈ Finset.range j, f r := by
      apply Finset.sum_bij (fun k _ => j - k)
      · intro k hk
        have hk' := Finset.mem_Icc.mp hk
        exact Finset.mem_range.mpr (by omega)
      · intro a ha b hb hab
        have ha' := Finset.mem_Icc.mp ha
        have hb' := Finset.mem_Icc.mp hb
        omega
      · intro r hr
        have hr' := Finset.mem_range.mp hr
        exact ⟨j - r, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro k hk
        have hk' := Finset.mem_Icc.mp hk
        have hidx : j + d - k = d + (j - k) := by omega
        have harg : (j : ℝ) - ((j - k : ℕ) : ℝ) = (k : ℝ) := by
          rw [Nat.cast_sub hk'.2]
          ring
        dsimp only [f, w, weightedBinomialWeight, P]
        rw [hidx, harg, ascPochhammer_nat_eq_natCast_ascFactorial]
        ring
    have htruncate : (∑ r ∈ Finset.range j, f r) =
        ∑ r ∈ Finset.range (m - d + 1), f r := by
      by_cases hle : j ≤ m - d + 1
      · apply Finset.sum_subset (Finset.range_mono hle)
        intro r hr hnot
        have hr' := Finset.mem_range.mp hr
        have hnr : j ≤ r := by simpa only [Finset.mem_range, not_lt] using hnot
        have hroot : r - j < 2 * m := by omega
        have harg : (j : ℝ) - (r : ℝ) = -((r - j : ℕ) : ℝ) := by
          rw [Nat.cast_sub hnr]
          ring
        dsimp only [f, P]
        rw [harg, ascPochhammer_eval_neg_coe_nat_of_lt hroot, mul_zero]
      · symm
        apply Finset.sum_subset (Finset.range_mono (by omega : m - d + 1 ≤ j))
        intro r _ hnot
        have hnr : m - d + 1 ≤ r := by simpa only [Finset.mem_range, not_lt] using hnot
        have hz : m.choose (d + r) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        simp only [f, w, weightedBinomialWeight, hz, Nat.cast_zero, mul_zero, zero_mul]
    rw [hreverse, htruncate]
    change weightedBinomialRisingSum m d (j : ℝ) = _
    simpa only [← Nat.cast_add, ascPochhammer_nat_eq_natCast_ascFactorial,
      mul_comm, mul_left_comm, mul_assoc] using weightedBinomialRisingSum_eq m d hm hd (j : ℝ)
  · have hz : (2 * m).choose (m + d) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hz, Nat.cast_zero, mul_zero]
    apply Finset.sum_eq_zero
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    have hzk : m.choose (j + d - k) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hzk, Nat.cast_zero, zero_mul, zero_mul]

#print axioms weightedBinomialRisingSum_recurrence
#print axioms weightedBinomialRisingSum_eq
#print axioms weightedBinomialInverse_identity

end MF21Restart
