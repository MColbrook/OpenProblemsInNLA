import MF21Restart.TraceSeriesOdd
import MF21Restart.TraceSeriesHalf

/-!
Irrationality of the actual normalized series in manuscript (31), using
the proved integer and half-integer tails (32)–(33) and π transcendence.
This module makes no assertion identifying a Toeplitz trace limit with it.
-/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

theorem half_integer_shift_trace_series_irrational (m r : ℕ)
    (hm : 1 ≤ m) (hr : 1 ≤ r) :
    Irrational ((Real.pi ^ (2 * m))⁻¹ *
      ∑' j : ℕ, (((j : ℝ) + (r : ℝ) + 1 / 2) ^ (2 * m))⁻¹) := by
  rw [(hasSum_half_integer_tail m r hm).tsum_eq]
  let u : ℚ := ((2 : ℚ) ^ (2 * m) - 1) * evenZetaRational m
  change Irrational ((Real.pi ^ (2 * m))⁻¹ *
    ((u : ℝ) * Real.pi ^ (2 * m) - (halfIntegerTailCorrection m r : ℝ)))
  have hpi : Real.pi ^ (2 * m) ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hvalue :
      (Real.pi ^ (2 * m))⁻¹ *
        ((u : ℝ) * Real.pi ^ (2 * m) - (halfIntegerTailCorrection m r : ℝ)) =
      (u : ℝ) - (halfIntegerTailCorrection m r : ℝ) / Real.pi ^ (2 * m) := by
    field_simp [hpi]
  rw [hvalue]
  exact trace_rational_form_irrational m hm u (halfIntegerTailCorrection m r)
    (halfIntegerTailCorrection_pos m r hr)

/-- The exact normalized series in (31) is irrational for every m≥3. -/
theorem trace_series_irrational (m : ℕ) (hm : 3 ≤ m) :
    Irrational ((Real.pi ^ (2 * m))⁻¹ *
      ∑' j : ℕ,
        (((j : ℝ) + 1 + ((m - 1 : ℕ) : ℝ) / 2) ^ (2 * m))⁻¹) := by
  rcases Nat.even_or_odd m with heven | hodd
  · obtain ⟨r, rfl⟩ := even_iff_exists_two_mul.mp heven
    have hr : 1 ≤ r := by omega
    have hnat : (2 * r - 1) + 1 = 2 * r := by omega
    have hcast := congrArg (fun n : ℕ => (n : ℝ)) hnat
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat] at hcast
    have hshift : 1 + (((2 * r - 1 : ℕ) : ℝ) / 2) = (r : ℝ) + 1 / 2 := by
      linarith
    simpa only [add_assoc, hshift] using
      half_integer_shift_trace_series_irrational (2 * r) r (by omega) hr
  · exact trace_series_irrational_of_odd m hm hodd

#print axioms half_integer_shift_trace_series_irrational
#print axioms trace_series_irrational

end MF21Restart
