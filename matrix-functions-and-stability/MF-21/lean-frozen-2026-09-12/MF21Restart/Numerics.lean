import LeanCert.Core.IntervalRat.Transcendental
import LeanCert.Tactic.Verification
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
The numerical target is unchanged: the phase-window margin follows from the
single closed lower bound `1 ≤ sqrt 2`. Use LeanCert's rational sqrt enclosure
at the explicitly fixed scale zero, which computes only `Nat.sqrt 2`, and
verify its value through LeanCert's kernel certificate boundary.
-/

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace MF21Restart

theorem phase_window_margin : (1 / 4 : ℝ) < Real.sin (Real.pi / 4) := by
  rw [Real.sin_pi_div_four]
  have hcert :
      LeanCert.Core.IntervalRat.sqrtRatLowerPrec (2 : ℚ) 0 = 1 := by
    leancert_verify_cert
  have hs : (1 : ℝ) ≤ Real.sqrt (2 : ℝ) := by
    have hsound := LeanCert.Core.IntervalRat.sqrtRatLowerPrec_le_sqrt
      (q := (2 : ℚ)) (by norm_num) 0
    simpa only [hcert, Rat.cast_one, Rat.cast_ofNat] using hsound
  linarith only [hs]

#assert_trust kernel phase_window_margin
#print axioms phase_window_margin

end MF21Restart
