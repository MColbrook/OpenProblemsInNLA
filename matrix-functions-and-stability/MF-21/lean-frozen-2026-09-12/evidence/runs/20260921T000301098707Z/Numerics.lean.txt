import LeanCert.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
The sole numerical target currently selected is the sign margin at the
endpoints of the phase windows in Lemma 4. Reduce the trigonometric constant
exactly, then certify a single algebraic constant in kernel mode.
-/

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace MF21Restart

theorem phase_window_margin : (1 / 4 : ℝ) < Real.sin (Real.pi / 4) := by
  rw [Real.sin_pi_div_four]
  have hs : (1 : ℚ) ≤ Real.sqrt (2 : ℝ) := by
    interval_decide (trust := kernel)
  have hs' : (1 : ℝ) ≤ Real.sqrt (2 : ℝ) := by exact_mod_cast hs
  linarith only [hs']

#print axioms phase_window_margin

end MF21Restart
