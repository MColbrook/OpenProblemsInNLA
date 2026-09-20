import MF21.MF21Transcendence.PiTranscendental
import Mathlib.NumberTheory.Real.Irrational

/-!
Unconditional arithmetic input for MF-21. The external, Apache-licensed
Lindemann proof has been ported and checked against this project's pinned
Mathlib. See `MF21Transcendence/provenance.json` and its `LICENSE`.

This module discharges transcendence of pi and the arithmetic trace mismatch.
It does not by itself establish either Toeplitz trace limit.
-/

namespace MF21Audit

/-- Lindemann's theorem for the actual real number pi, with no hypotheses. -/
theorem pi_transcendental : Transcendental ℚ Real.pi :=
  LeanFormalizations.Transcendence.transcendental_pi_axiomClean

/-- Every positive natural power of pi is irrational. -/
theorem pi_pow_irrational (k : ℕ) (hk : 0 < k) :
    Irrational (Real.pi ^ k) :=
  (pi_transcendental.pow hk).irrational

/-- A nonzero rational correction divided by a positive power of pi is
irrational; all transcendence inputs are now proved. -/
theorem pi_trace_value_irrational (u v : ℚ) (hv : v ≠ 0)
    (k : ℕ) (hk : 0 < k) :
    Irrational ((u : ℝ) - (v : ℝ) / Real.pi ^ k) :=
  ((pi_pow_irrational k hk).ratCast_div hv).ratCast_sub u

/-- Unconditional arithmetic inequality used by the MF-21 trace argument. -/
theorem trace_values_ne_unconditional (m : ℕ) (hm : 0 < m)
    (c u v : ℚ) (hv : 0 < v) :
    (c : ℝ) ≠ (u : ℝ) - (v : ℝ) / Real.pi ^ (2 * m) := by
  have hirr := pi_trace_value_irrational u v (ne_of_gt hv) (2 * m)
    (Nat.mul_pos (by decide) hm)
  intro heq
  exact hirr ⟨c, heq⟩

end MF21Audit

#print axioms MF21Audit.pi_transcendental
#print axioms MF21Audit.pi_pow_irrational
#print axioms MF21Audit.pi_trace_value_irrational
#print axioms MF21Audit.trace_values_ne_unconditional
