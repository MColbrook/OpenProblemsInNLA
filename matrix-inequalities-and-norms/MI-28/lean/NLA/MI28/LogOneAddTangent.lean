/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

The scalar tangent inequality is a direct consequence of Mathlib's weighted
arithmetic-geometric mean inequality, with weights 1/(1+a), a/(1+a) and
positive entries 1, b/a. Taking logarithms gives the required inequality.
-/
import NLA.MI28.Definitions
import Mathlib.Analysis.MeanInequalities

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace NLA.MI28

/-- C16: the supporting-line inequality for log(1+exp), in positive coordinates. -/
theorem log_one_add_tangent (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.log (1 + a) - Real.log (1 + b) ≤
      a / (1 + a) * (Real.log a - Real.log b) := by
  have h1a : 0 < 1 + a := by linarith
  have h1b : 0 < 1 + b := by linarith
  have hweights : 1 / (1 + a) + a / (1 + a) = 1 := by
    field_simp [ne_of_gt h1a]
  have hmean := Real.geom_mean_le_arith_mean2_weighted
    (w₁ := 1 / (1 + a)) (w₂ := a / (1 + a)) (p₁ := 1) (p₂ := b / a)
    (by positivity) (by positivity) (by norm_num) (div_pos hb ha).le hweights
  simp only [Real.one_rpow, one_mul, mul_one] at hmean
  have hsum : 1 / (1 + a) + a / (1 + a) * (b / a) = (1 + b) / (1 + a) := by
    field_simp [ne_of_gt h1a, ne_of_gt ha] <;> ring
  rw [hsum] at hmean
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos (div_pos hb ha) _) hmean
  rw [Real.log_rpow (div_pos hb ha), Real.log_div (ne_of_gt hb) (ne_of_gt ha),
    Real.log_div (ne_of_gt h1b) (ne_of_gt h1a)] at hlog
  nlinarith

end NLA.MI28
