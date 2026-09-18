/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

The k >= 2 range of Ghabries, Abbas, Mourad and Assi (2020), Lemma 2.5,
can be proved for the required positive-definite matrices entirely in order form.
Set D = B A^2 B. From D^(p/2) <= A^k, raise by 2/k and conjugate by B.
PositiveProductOrder then gives B^2 <= D^(1-p/k). Raising this by p/2 and
the original hypothesis by 1-p/k completes B^p <= A^(k-p).

To obtain frozen C12, the future modulus bridge identifies D with |AB|^2,
and the common OrderImplication-to-norm normalization used by C11 applies.
This file proves the matrix-order core without assuming either pending bridge.
It needs neither a separate Cordes norm theorem nor any additional computation.
-/
import NLA.MI28.PositiveProductOrder

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI28

open NLA.MI24 (spectralPower_posDef posDef_hermitian_sandwich spectralPower_comp
  spectralPower_order hermitian_sandwich_order)

local notation "fpow" => NLA.MI24.spectralPower

/-- Large-base matrix-order core, before the exact product-modulus identification. -/
lemma large_base_sandwich_order {n : ℕ} (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (k p : ℝ)
    (hk : 2 ≤ k) (hp0 : 0 ≤ p) (hp2 : p ≤ 2)
    (h : fpow (B * fpow A 2 * B) (p / 2) ≤ fpow A k) :
    fpow B p ≤ fpow A (k - p) := by
  let D := B * fpow A 2 * B
  have hD : D.PosDef := posDef_hermitian_sandwich _ _
    (spectralPower_posDef A hA _) hB.isHermitian hB.isUnit
  have hk0 : 0 < k := by linarith
  have hpk0 : 0 ≤ p / k := div_nonneg hp0 hk0.le
  have hpk1 : p / k ≤ 1 := by
    apply (div_le_iff₀ hk0).mpr
    linarith
  have htwo0 : 0 ≤ 2 / k := div_nonneg (by norm_num) hk0.le
  have htwo1 : 2 / k ≤ 1 := by
    apply (div_le_iff₀ hk0).mpr
    linarith

  -- The large-base condition makes 2/k an operator-monotone exponent.
  have hbase : fpow D (p / 2) ≤ fpow A k := h
  have hsmall := spectralPower_order _ _ hbase (2 / k) htwo0 htwo1
  rw [spectralPower_comp D hD, spectralPower_comp A hA] at hsmall
  have hexpD : p / 2 * (2 / k) = p / k := by ring
  have hexpA : k * (2 / k) = 2 := by field_simp [ne_of_gt hk0]
  rw [hexpD, hexpA] at hsmall
  have hproduct : B * fpow D (p / k) * B ≤ D :=
    hermitian_sandwich_order _ _ B hsmall hB.isHermitian
  have hBsq := positive_product_order B D hB hD (p / k) 1 hpk0
    (by norm_num) (by
      -- The contraction helper writes its right side as the first power of D.
      simpa only [NLA.MI24.spectralPower_one D hD] using hproduct)

  -- Two powers in [0,1] connect the recovered square to the desired comparison.
  have hhalf0 : 0 ≤ p / 2 := by linarith
  have hhalf1 : p / 2 ≤ 1 := by linarith
  have hrest0 : 0 ≤ 1 - p / k := sub_nonneg.mpr hpk1
  have hrest1 : 1 - p / k ≤ 1 := by linarith
  have hBpowtwo : fpow B 2 = B * B := by
    simpa [NLA.MI24.spectralPower, CFC.rpow_eq_pow, pow_two] using
      CFC.rpow_natCast B 2 hB.posSemidef.nonneg
  rw [← hBpowtwo] at hBsq
  have hleft := spectralPower_order _ _ hBsq (p / 2) hhalf0 hhalf1
  rw [spectralPower_comp B hB, spectralPower_comp D hD] at hleft
  have hleftExp : 2 * (p / 2) = p := by ring
  rw [hleftExp] at hleft
  have hright := spectralPower_order _ _ hbase (1 - p / k) hrest0 hrest1
  rw [spectralPower_comp D hD, spectralPower_comp A hA] at hright
  have hmid : (1 - p / k) * (p / 2) = (p / 2) * (1 - p / k) := mul_comm _ _
  have hout : k * (1 - p / k) = k - p := by
    field_simp [ne_of_gt hk0] <;> ring
  rw [hmid] at hleft
  rw [hout] at hright
  exact hleft.trans hright

end NLA.MI28
