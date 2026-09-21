import MF21Restart.TraceSeriesZeta
import MF21Restart.TraceIrrationality

/-!
The actual normalized trace series is irrational in the odd-order case of
manuscript (32). The finite correction and the series identity are derived
in TraceSeriesZeta; no rational-minus form is assumed here.
-/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

theorem integer_shift_trace_series_irrational (m r : ℕ)
    (hm : 1 ≤ m) (hr : 1 ≤ r) :
    Irrational ((Real.pi ^ (2 * m))⁻¹ *
      ∑' j : ℕ, (((j : ℝ) + 1 + (r : ℝ)) ^ (2 * m))⁻¹) := by
  rw [(hasSum_integer_tail m r hm).tsum_eq]
  have hpi : Real.pi ^ (2 * m) ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hvalue :
      (Real.pi ^ (2 * m))⁻¹ *
        ((evenZetaRational m : ℝ) * Real.pi ^ (2 * m) -
          (integerTailCorrection m r : ℝ)) =
      (evenZetaRational m : ℝ) -
        (integerTailCorrection m r : ℝ) / Real.pi ^ (2 * m) := by
    field_simp [hpi]
  rw [hvalue]
  exact trace_rational_form_irrational m hm (evenZetaRational m)
    (integerTailCorrection m r) (integerTailCorrection_pos m r hr)

/-- The unchanged series from (31), for odd m≥3, by the tail identity (32). -/
theorem trace_series_irrational_of_odd (m : ℕ)
    (hm : 3 ≤ m) (hodd : Odd m) :
    Irrational ((Real.pi ^ (2 * m))⁻¹ *
      ∑' j : ℕ,
        (((j : ℝ) + 1 + ((m - 1 : ℕ) : ℝ) / 2) ^ (2 * m))⁻¹) := by
  obtain ⟨r, rfl⟩ := odd_iff_exists_bit1.mp hodd
  have hr : 1 ≤ r := by omega
  have hshift : (((2 * r + 1 - 1 : ℕ) : ℝ) / 2) = (r : ℝ) := by
    rw [show 2 * r + 1 - 1 = 2 * r by omega]
    push_cast
    ring
  simpa only [hshift] using
    integer_shift_trace_series_irrational (2 * r + 1) r (by omega) hr

#print axioms integer_shift_trace_series_irrational
#print axioms trace_series_irrational_of_odd

end MF21Restart
