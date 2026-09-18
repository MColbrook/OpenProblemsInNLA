/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

The exact small-base implication is passed to the common positive-scaling
argument, yielding the concrete Euclidean operator-norm comparison.
-/
import NLA.MI28.SmallBaseImplication
import NLA.MI28.NormComparison

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI28

/-- C11: the full small-base norm range, with both upper endpoints included. -/
theorem small_base_norm {n : ℕ} (hn : 1 ≤ n) (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (k p : ℝ)
    (hk0 : 0 < k) (hk2 : k ≤ 2) (hp0 : 0 < p) (hp2 : p ≤ 2) :
    operatorNorm (normalizedH A B k p) ≤ operatorNorm (normalizedZ A B k p) := by
  exact norm_comparison_of_order_implication k p hp0
    (small_base_implication k p hk0 hk2 hp0 hp2) hn A B hA hB

end NLA.MI28
