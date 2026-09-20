import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
Arithmetic and limit-comparison components of the MF-21 trace argument.

This is NOT a formalization of MF-21. In particular, transcendence of pi is an
explicit hypothesis, and the analytic trace limits must be supplied separately.
No theorem below asserts facts about Toeplitz matrices or their eigenvalues.
-/

namespace MF21Audit

/-- A nonzero rational correction divided by a positive power of a
transcendental real cannot leave a rational number. -/
theorem rational_sub_div_pow_irrational (t : ℝ) (ht : Transcendental ℚ t)
    (u v : ℚ) (hv : v ≠ 0) (k : ℕ) (hk : 0 < k) :
    Irrational ((u : ℝ) - (v : ℝ) / t ^ k) :=
  ((ht.pow hk).irrational.ratCast_div hv).ratCast_sub u

/-- The final arithmetic contradiction in Section 5, conditional on the
explicit transcendence input. -/
theorem trace_values_ne (m : ℕ) (hm : 0 < m) (c u v : ℚ) (hv : 0 < v)
    (hpi : Transcendental ℚ Real.pi) :
    (c : ℝ) ≠ (u : ℝ) - (v : ℝ) / Real.pi ^ (2 * m) := by
  have hirr := rational_sub_div_pow_irrational Real.pi hpi u v (ne_of_gt hv)
    (2 * m) (Nat.mul_pos (by decide) hm)
  intro heq
  exact hirr ⟨c, heq⟩

/-- Any sequence has at most one real limit. Thus the two trace-limit formulas
would be contradictory, once independently established. -/
theorem trace_limits_inconsistent (a : ℕ → ℝ)
    (m : ℕ) (hm : 0 < m) (c u v : ℚ) (hv : 0 < v)
    (hpi : Transcendental ℚ Real.pi)
    (hkernel : Filter.Tendsto a Filter.atTop (nhds (c : ℝ)))
    (hspectral : Filter.Tendsto a Filter.atTop
      (nhds ((u : ℝ) - (v : ℝ) / Real.pi ^ (2 * m)))) : False := by
  exact trace_values_ne m hm c u v hv hpi (tendsto_nhds_unique hkernel hspectral)

/-- A low-order upper bound on a remainder cannot establish that the next
order fails: the identically zero remainder satisfies both bounds. -/
theorem zero_remainder_satisfies_both_orders (h : ℝ) (hh : 0 ≤ h) (k : ℕ) :
    |(0 : ℝ)| ≤ h ^ k ∧ |(0 : ℝ)| ≤ h ^ (k + 1) := by
  simpa only [abs_zero] using And.intro (pow_nonneg hh k) (pow_nonneg hh (k + 1))

end MF21Audit

#print axioms MF21Audit.rational_sub_div_pow_irrational
#print axioms MF21Audit.trace_values_ne
#print axioms MF21Audit.trace_limits_inconsistent
#print axioms MF21Audit.zero_remainder_satisfies_both_orders
