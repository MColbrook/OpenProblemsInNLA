/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

Canonical Lemma 3 chooses s=p(k+2)/(k+p) and q=2/s. Exact real algebra proves
Furuta admissibility, and HigherPowerOrder supplies the internal negative-power
argument. Both p=1 and p=2 remain in the statement and proof.
-/
import NLA.MI28.HigherPowerOrder

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI28

local notation "fpow" => NLA.MI24.spectralPower

/-- C08: the full higher-power Furuta implication, including both endpoints. -/
theorem higher_power_implication (k p : ℝ) (hk : 0 < k)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2) : OrderImplication k p := by
  intro n _ A B hA hB h
  let s := p * (k + 2) / (k + p)
  have hp0 : 0 < p := by linarith
  have hK : 0 < k + 2 := by linarith
  have hkp : 0 < k + p := by linarith
  have hs : 0 < s := div_pos (mul_pos hp0 hK) hkp
  have hs2 : s ≤ 2 := by
    dsimp only [s]
    apply (div_le_iff₀ hkp).mpr
    nlinarith [mul_nonneg hk.le (sub_nonneg.mpr hp2)]
  have hq : 1 ≤ 2 / s := (le_div_iff₀ hs).mpr (by simpa using hs2)
  have hadmEq : (1 + 2 / k) * (2 / s) = 2 / p + 2 / k := by
    dsimp only [s]
    field_simp [ne_of_gt hk, ne_of_gt hp0, ne_of_gt hK, ne_of_gt hkp] <;> ring
  have hraw : fpow (matrixModulus (A * B)) p ≤ fpow A k := by
    simpa only [spectralPower, NLA.MI24.spectralPower] using h
  have hF := furuta_square_order A B hA hB k p (2 / s) hk hp0 hp2 hq
    (le_of_eq hadmEq.symm) hraw
  have hleft : 2 / (2 / s) = s := by field_simp [ne_of_gt hs]
  have hright : (2 * k / p + 2) / (2 / s) = k + 2 := by
    dsimp only [s]
    field_simp [ne_of_gt hp0, ne_of_gt hK, ne_of_gt hkp] <;> ring
  rw [hleft, hright] at hF
  have hfinal := higher_power_sandwich_order A B hA hB k p hk hp1 hp2 hF
  simpa only [spectralPower, NLA.MI24.spectralPower] using hfinal

end NLA.MI28
