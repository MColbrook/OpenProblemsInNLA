import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

/-!
Euler's even-zeta value and the integer tail in manuscript (32).
TRACE_SERIES_STATEMENTS.md was locked before these proofs. All infinite
series identities are proved as HasSum statements before any tsum is used.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

/-- The explicit rational coefficient in Euler's even-zeta formula. -/
def evenZetaRational (m : ℕ) : ℚ :=
  (-1 : ℚ) ^ (m + 1) * (2 : ℚ) ^ (2 * m - 1) *
    bernoulli (2 * m) / ((2 * m).factorial : ℚ)

/-- The finite rational subtraction over the positive integers 1,...,r. -/
def integerTailCorrection (m r : ℕ) : ℚ :=
  ∑ j ∈ Finset.range r, (((j : ℚ) + 1) ^ (2 * m))⁻¹

theorem hasSum_even_zeta (m : ℕ) (hm : 1 ≤ m) :
    HasSum (fun n : ℕ => ((n : ℝ) ^ (2 * m))⁻¹)
      ((evenZetaRational m : ℝ) * Real.pi ^ (2 * m)) := by
  have h := hasSum_zeta_nat (k := m) (by omega : m ≠ 0)
  have hvalue :
      (-1 : ℝ) ^ (m + 1) * (2 : ℝ) ^ (2 * m - 1) * Real.pi ^ (2 * m) *
        (bernoulli (2 * m) : ℝ) / ((2 * m).factorial : ℝ) =
      (evenZetaRational m : ℝ) * Real.pi ^ (2 * m) := by
    unfold evenZetaRational
    push_cast
    ring
  rw [hvalue] at h
  simpa only [one_div] using h

/-- The n=0 term in the even-zeta sum is zero, since the exponent is positive. -/
theorem hasSum_even_zeta_positive (m : ℕ) (hm : 1 ≤ m) :
    HasSum (fun j : ℕ => (((j : ℝ) + 1) ^ (2 * m))⁻¹)
      ((evenZetaRational m : ℝ) * Real.pi ^ (2 * m)) := by
  have h := (hasSum_nat_add_iff' 1).2 (hasSum_even_zeta m hm)
  simpa only [Finset.sum_range_one, Nat.cast_zero,
    zero_pow (by omega : 2 * m ≠ 0), inv_zero, sub_zero,
    Nat.cast_add, Nat.cast_one] using h

theorem integerTailCorrection_cast (m r : ℕ) :
    (integerTailCorrection m r : ℝ) =
      ∑ j ∈ Finset.range r, (((j : ℝ) + 1) ^ (2 * m))⁻¹ := by
  simp only [integerTailCorrection, Rat.cast_sum, Rat.cast_inv, Rat.cast_pow,
    Rat.cast_add, Rat.cast_natCast, Rat.cast_one]

/-- Equation (32), with an arbitrary even exponent and integer shift r. -/
theorem hasSum_integer_tail (m r : ℕ) (hm : 1 ≤ m) :
    HasSum (fun j : ℕ => (((j : ℝ) + 1 + (r : ℝ)) ^ (2 * m))⁻¹)
      ((evenZetaRational m : ℝ) * Real.pi ^ (2 * m) -
        (integerTailCorrection m r : ℝ)) := by
  have h := (hasSum_nat_add_iff' r).2 (hasSum_even_zeta_positive m hm)
  convert! h using 1
  · funext j
    push_cast
    congr 2 <;> ring
  · rw [integerTailCorrection_cast]

theorem integerTailCorrection_pos (m r : ℕ) (hr : 1 ≤ r) :
    0 < integerTailCorrection m r := by
  unfold integerTailCorrection
  apply Finset.sum_pos
  · intro j _
    positivity
  · exact ⟨0, Finset.mem_range.mpr (by omega)⟩

#print axioms hasSum_even_zeta
#print axioms hasSum_even_zeta_positive
#print axioms hasSum_integer_tail
#print axioms integerTailCorrection_pos

end MF21Restart
