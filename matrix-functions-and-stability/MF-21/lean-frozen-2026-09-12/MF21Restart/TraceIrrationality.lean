import MF21Restart.PiTranscendence
import Mathlib.NumberTheory.Real.Irrational

/-! The final arithmetic inference in manuscript Section 5, using a proved
transcendence dependency. Identification of the trace series is separate. -/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

theorem rational_sub_div_pi_pow_irrational (k : ℕ) (hk : 0 < k)
    (u v : ℚ) (hv : v ≠ 0) :
    Irrational ((u : ℝ) - (v : ℝ) / Real.pi ^ k) := by
  exact ((pi_transcendental.pow hk).irrational.ratCast_div hv).ratCast_sub u

theorem trace_rational_form_irrational (m : ℕ) (hm : 1 ≤ m)
    (u v : ℚ) (hv : 0 < v) :
    Irrational ((u : ℝ) - (v : ℝ) / Real.pi ^ (2 * m)) := by
  exact rational_sub_div_pi_pow_irrational (2 * m) (by omega) u v (ne_of_gt hv)

#print axioms rational_sub_div_pi_pow_irrational
#print axioms trace_rational_form_irrational

end MF21Restart
