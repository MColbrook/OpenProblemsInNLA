/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

Canonical Lemma 2: q=2 in the common Furuta substitution gives
ABA <= A^(1+k/p). Inverse congruence gives B <= A^(k/p-1), and
Loewner-Heinz at p in (0,1] concludes the exact frozen order implication.
-/
import NLA.MI28.FurutaSubstitution

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI28

open NLA.MI24 (spectralPower_comp spectralPower_one spectralPower_isHermitian
  spectralPower_sandwich_same spectralPower_order hermitian_sandwich_order
  posDef_hermitian_sandwich)

local notation "fpow" => NLA.MI24.spectralPower

/-- C07: the complete lower-power parameter region of the canonical solution. -/
theorem lower_power_implication (k p : ℝ) (hk : 0 < k)
    (hp0 : 0 < p) (hpl : k / (k + 1) ≤ p) (hpu : p ≤ 1) :
    OrderImplication k p := by
  intro n _ A B hA hB h
  have hmul : k ≤ p * (k + 1) := (div_le_iff₀ (by linarith : 0 < k + 1)).mp hpl
  have hrec : 1 / p ≤ (k + 1) / k := by
    apply (div_le_div_iff₀ hp0 hk).mpr
    nlinarith
  have hratio : (k + 1) / k = 1 + 1 / k := by
    field_simp [ne_of_gt hk] <;> ring
  rw [hratio] at hrec
  have hadm : 2 / p + 2 / k ≤ (1 + 2 / k) * 2 := by
    calc
      2 / p + 2 / k = 2 * (1 / p) + 2 / k := by ring
      _ ≤ 2 * (1 + 1 / k) + 2 / k := by linarith
      _ = (1 + 2 / k) * 2 := by ring
  have hraw : fpow (matrixModulus (A * B)) p ≤ fpow A k := by
    simpa only [spectralPower, NLA.MI24.spectralPower] using h
  have hF := furuta_square_order A B hA hB k p 2 hk hp0
    (by linarith) (by norm_num) hadm hraw
  have hC := posDef_hermitian_sandwich B A hB hA.isHermitian hA.isUnit
  have htwo : (2 : ℝ) / 2 = 1 := by norm_num
  have hright : (2 * k / p + 2) / 2 = k / p + 1 := by ring
  rw [htwo, spectralPower_one _ hC, hright] at hF

  -- Conjugation removes the two outer factors A without changing factor order.
  have hconj := hermitian_sandwich_order _ _ (fpow A (-1)) hF
    (spectralPower_isHermitian A hA _)
  rw [inverse_congruence_cancel A B hA, spectralPower_sandwich_same A hA] at hconj
  have hexp : 2 * (-1 : ℝ) + (k / p + 1) = k / p - 1 := by ring
  rw [hexp] at hconj
  have hpow := spectralPower_order _ _ hconj p hp0.le hpu
  rw [spectralPower_comp A hA] at hpow
  have hout : (k / p - 1) * p = k - p := by
    field_simp [ne_of_gt hp0] <;> ring
  rw [hout] at hpow
  simpa only [spectralPower, NLA.MI24.spectralPower] using hpow

end NLA.MI28
