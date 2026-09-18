/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

The parameter split in the canonical MI28 solution uses C08 for p>=1 and
C07 for k/(k+1)<=p<=1. Below that threshold p<k, so C09 applies one of the
same two already proved lemmas to the swapped parameters. No recursion or
parameter grid is needed, and each boundary belongs to a closed branch.
-/
import NLA.MI28.LowerPowerImplication
import NLA.MI28.HigherPowerImplication
import NLA.MI28.SwapImplication

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI28

/-- C10: all strictly positive parameters in the complete small-base rectangle. -/
theorem small_base_implication (k p : ℝ) (hk0 : 0 < k) (hk2 : k ≤ 2)
    (hp0 : 0 < p) (hp2 : p ≤ 2) : OrderImplication k p := by
  by_cases hp1 : 1 ≤ p
  · exact higher_power_implication k p hk0 hp1 hp2
  have hplt : p < 1 := lt_of_not_ge hp1
  by_cases hpl : k / (k + 1) ≤ p
  · exact lower_power_implication k p hk0 hp0 hpl hplt.le

  -- Below the lower-power threshold the swap is admissible because p<k.
  have hthreshold : k / (k + 1) < k := by
    apply (div_lt_iff₀ (by linarith : 0 < k + 1)).mpr
    nlinarith [sq_pos_of_pos hk0]
  have hpk : p ≤ k := ((lt_of_not_ge hpl).trans hthreshold).le
  apply swap_implication k p hp0 hpk
  by_cases hk1 : k ≤ 1
  · have hswapLower : p / (p + 1) ≤ k := by
      calc
        p / (p + 1) ≤ p := by
          apply (div_le_iff₀ (by linarith : 0 < p + 1)).mpr
          nlinarith [sq_nonneg p]
        _ ≤ k := hpk
    exact lower_power_implication p k hp0 hk0 hswapLower hk1
  · exact higher_power_implication p k hp0 (lt_of_not_ge hk1).le hk2

end NLA.MI28
