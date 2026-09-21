import MF21Restart.TraceSeriesZeta
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
The half-integer tail in manuscript (33). The factor 2^(2m)-1 is derived
from the even/odd partition of the actual summable integer zeta series.
The finite correction retains the factor 2^(2m) from odd denominators.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

/-- The literal finite rational correction in manuscript (33). -/
def halfIntegerTailCorrection (m r : ℕ) : ℚ :=
  (2 : ℚ) ^ (2 * m) *
    ∑ j ∈ Finset.range r, ((2 * (j : ℚ) + 1) ^ (2 * m))⁻¹

private lemma reciprocal_half_power (p : ℕ) (x : ℝ) :
    ((x + 1 / 2) ^ p)⁻¹ = (2 : ℝ) ^ p * ((2 * x + 1) ^ p)⁻¹ := by
  rw [show x + 1 / 2 = (2 * x + 1) / 2 by ring,
    div_pow, inv_div, div_eq_mul_inv]

/-- The half-integer zeta series, obtained by separating even and odd indices. -/
theorem hasSum_half_integer_zeta (m : ℕ) (hm : 1 ≤ m) :
    HasSum (fun j : ℕ => (((j : ℝ) + 1 / 2) ^ (2 * m))⁻¹)
      (((((2 : ℚ) ^ (2 * m) - 1) * evenZetaRational m : ℚ) : ℝ) *
        Real.pi ^ (2 * m)) := by
  have heven :
      HasSum (fun j : ℕ => (((2 * j : ℕ) : ℝ) ^ (2 * m))⁻¹)
        ((evenZetaRational m : ℝ) * Real.pi ^ (2 * m) / (2 : ℝ) ^ (2 * m)) := by
    convert! (hasSum_even_zeta m hm).div_const ((2 : ℝ) ^ (2 * m)) using 1
    funext j
    simp only [Nat.cast_mul, Nat.cast_ofNat, mul_pow, mul_inv_rev, div_eq_mul_inv]
  have hodd : Summable (fun j : ℕ => (((2 * j + 1 : ℕ) : ℝ) ^ (2 * m))⁻¹) :=
    (hasSum_even_zeta m hm).summable.comp_injective
      (i := fun j : ℕ => 2 * j + 1) (by
        intro a b h
        change 2 * a + 1 = 2 * b + 1 at h
        omega)
  have hsplit := HasSum.even_add_odd
    (f := fun n : ℕ => ((n : ℝ) ^ (2 * m))⁻¹) heven hodd.hasSum
  have hoddvalue :
      (∑' j : ℕ, (((2 * j + 1 : ℕ) : ℝ) ^ (2 * m))⁻¹) =
        (evenZetaRational m : ℝ) * Real.pi ^ (2 * m) -
          (evenZetaRational m : ℝ) * Real.pi ^ (2 * m) / (2 : ℝ) ^ (2 * m) := by
    have h := hsplit.unique (hasSum_even_zeta m hm)
    linarith
  convert! hodd.hasSum.mul_left ((2 : ℝ) ^ (2 * m)) using 1
  · funext j
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    exact reciprocal_half_power (2 * m) (j : ℝ)
  · rw [hoddvalue]
    push_cast
    have htwo : (2 : ℝ) ^ (2 * m) ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp [htwo] <;> ring

theorem halfIntegerTailCorrection_cast (m r : ℕ) :
    (halfIntegerTailCorrection m r : ℝ) =
      ∑ j ∈ Finset.range r, (((j : ℝ) + 1 / 2) ^ (2 * m))⁻¹ := by
  simp only [halfIntegerTailCorrection, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat,
    Rat.cast_sum, Rat.cast_inv, Rat.cast_add, Rat.cast_natCast, Rat.cast_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (reciprocal_half_power (2 * m) (j : ℝ)).symm

/-- Equation (33), with its full positive finite odd-denominator correction. -/
theorem hasSum_half_integer_tail (m r : ℕ) (hm : 1 ≤ m) :
    HasSum (fun j : ℕ => (((j : ℝ) + (r : ℝ) + 1 / 2) ^ (2 * m))⁻¹)
      (((((2 : ℚ) ^ (2 * m) - 1) * evenZetaRational m : ℚ) : ℝ) *
        Real.pi ^ (2 * m) - (halfIntegerTailCorrection m r : ℝ)) := by
  have h := (hasSum_nat_add_iff' r).2 (hasSum_half_integer_zeta m hm)
  convert! h using 1
  · funext j
    simp only [Nat.cast_add]
  · rw [halfIntegerTailCorrection_cast]

theorem halfIntegerTailCorrection_pos (m r : ℕ) (hr : 1 ≤ r) :
    0 < halfIntegerTailCorrection m r := by
  unfold halfIntegerTailCorrection
  apply mul_pos (pow_pos (by norm_num) _)
  apply Finset.sum_pos
  · intro j _
    positivity
  · exact ⟨0, Finset.mem_range.mpr (by omega)⟩

#print axioms hasSum_half_integer_zeta
#print axioms hasSum_half_integer_tail
#print axioms halfIntegerTailCorrection_pos

end MF21Restart
