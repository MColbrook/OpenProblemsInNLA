/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

The frozen large-base contract joins the internal Ghabries-range order proof
to the common concrete norm normalization. No literature statement is assumed.
-/
import NLA.MI28.LargeBaseImplication
import NLA.MI28.NormComparison

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI28

/-- C12: all real k >= 2 and 0 < p <= 2, for the genuine Euclidean norms. -/
theorem large_base_norm {n : ℕ} (hn : 1 ≤ n) (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (k p : ℝ)
    (hk : 2 ≤ k) (hp0 : 0 < p) (hp2 : p ≤ 2) :
    operatorNorm (normalizedH A B k p) ≤ operatorNorm (normalizedZ A B k p) := by
  exact norm_comparison_of_order_implication k p hp0
    (large_base_implication k p hk hp0.le hp2) hn A B hA hB

end NLA.MI28
