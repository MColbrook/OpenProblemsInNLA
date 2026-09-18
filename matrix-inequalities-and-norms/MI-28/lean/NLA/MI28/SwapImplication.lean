/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

Canonical Lemma 5 applies the proved universal implication at swapped
parameters to (|AB|^(-1), B). C03 gives its exact modulus. Two powers in [0,1]
then return to the original parameters, including the zero exponent when p=k.
-/
import NLA.MI28.SwappedModulus

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI28

open NLA.MI24 (spectralPower_posDef spectralPower_comp spectralPower_order
  spectralPower_inverse_order)

local notation "fpow" => NLA.MI24.spectralPower

/-- C09: the exact universally quantified parameter swap, including p=k. -/
theorem swap_implication (k p : ℝ) (hp : 0 < p) (hpk : p ≤ k)
    (hswap : OrderImplication p k) : OrderImplication k p := by
  intro n hn A B hA hB h
  let M := matrixModulus (A * B)
  let A' := fpow M (-1)
  have hM : M.PosDef := matrixModulus_posDef _ (hA.isUnit.mul hB.isUnit)
  have hA' : A'.PosDef := spectralPower_posDef M hM _
  have hk : 0 < k := lt_of_lt_of_le hp hpk
  have hraw : fpow M p ≤ fpow A k := by
    simpa only [M, spectralPower, NLA.MI24.spectralPower] using h

  -- Inversion gives precisely the premise for the swapped pair, using C03.
  have hinv := spectralPower_inverse_order _ _ (spectralPower_posDef M hM p) hraw
  rw [spectralPower_comp A hA, spectralPower_comp M hM] at hinv
  have hmod : matrixModulus (A' * B) = fpow A (-1) := by
    simpa only [A', M, spectralPower, NLA.MI24.spectralPower] using
      swapped_modulus A B hA hB
  have hprem : fpow (matrixModulus (A' * B)) k ≤ fpow A' p := by
    rw [hmod]
    dsimp only [A']
    rw [spectralPower_comp A hA, spectralPower_comp M hM]
    simpa only [neg_one_mul, mul_neg_one] using hinv
  have hpost := hswap n hn A' B hA' hB (by
    simpa only [spectralPower, NLA.MI24.spectralPower] using hprem)
  have hswapped : fpow B k ≤ fpow M (k - p) := by
    have hrawPost : fpow B k ≤ fpow A' (p - k) := by
      simpa only [spectralPower, NLA.MI24.spectralPower] using hpost
    dsimp only [A'] at hrawPost
    rw [spectralPower_comp M hM] at hrawPost
    have hexp : (-1 : ℝ) * (p - k) = k - p := by ring
    rwa [hexp] at hrawPost

  -- Both real powers are admitted at their closed endpoints; no strict gap is used.
  have hpk0 : 0 ≤ p / k := div_nonneg hp.le hk.le
  have hpk1 : p / k ≤ 1 := (div_le_iff₀ hk).mpr (by simpa using hpk)
  have hrest0 : 0 ≤ (k - p) / k := div_nonneg (sub_nonneg.mpr hpk) hk.le
  have hrest1 : (k - p) / k ≤ 1 := by
    apply (div_le_iff₀ hk).mpr
    linarith
  have hleft := spectralPower_order _ _ hswapped (p / k) hpk0 hpk1
  have hright := spectralPower_order _ _ hraw ((k - p) / k) hrest0 hrest1
  rw [spectralPower_comp B hB, spectralPower_comp M hM] at hleft
  rw [spectralPower_comp M hM, spectralPower_comp A hA] at hright
  have hleftExp : k * (p / k) = p := by field_simp [ne_of_gt hk]
  have hmiddle : (k - p) * (p / k) = p * ((k - p) / k) := by ring
  have hrightExp : k * ((k - p) / k) = k - p := by field_simp [ne_of_gt hk]
  rw [hleftExp, hmiddle] at hleft
  rw [hrightExp] at hright
  have hfinal := hleft.trans hright
  simpa only [spectralPower, NLA.MI24.spectralPower] using hfinal

end NLA.MI28
