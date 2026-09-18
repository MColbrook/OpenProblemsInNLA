/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

The negative-power step in canonical MI28 Lemma 3 is proved internally from
Loewner-Heinz and the unchanged MI24 polar-power identity. It is not imported
as a negative-Furuta assumption. Starting with C^s <= A^(k+2), C=ABA,
the polar factor A^(-1) C^(1/2) exposes B^p and keeps every factor ordered.
-/
import NLA.MI28.FurutaSubstitution

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI28

open NLA.MI24 (spectralPower_posDef spectralPower_isHermitian spectralPower_comp
  spectralPower_mul spectralPower_half_mul_self spectralPower_sandwich_same
  spectralPower_order spectralPower_negative_order hermitian_sandwich_order
  spectralPower_mul_star_conjugation posDef_hermitian_sandwich)

local notation "fpow" => NLA.MI24.spectralPower

lemma higher_power_sandwich_order {n : ℕ} (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (k p : ℝ) (hk : 0 < k)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (h : fpow (A * B * A) (p * (k + 2) / (k + p)) ≤ fpow A (k + 2)) :
    fpow B p ≤ fpow A (k - p) := by
  let C := A * B * A
  let s := p * (k + 2) / (k + p)
  let t := (k - p + 2) / (k + 2)
  have hC : C.PosDef := posDef_hermitian_sandwich B A hB hA.isHermitian hA.isUnit
  have hCs : fpow C s ≤ fpow A (k + 2) := h
  have hK : 0 < k + 2 := by linarith
  have hkp : 0 < k + p := by linarith
  have hneg0 : -1 ≤ -2 / (k + 2) := by
    apply (le_div_iff₀ hK).mpr
    linarith
  have hneg1 : -2 / (k + 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by norm_num) hK.le

  -- One proved negative-power order comparison supplies A^(-2) <= C^(-2p/(k+p)).
  have hneg := spectralPower_negative_order _ _
    (spectralPower_posDef C hC s) (spectralPower_posDef A hA (k + 2)) hCs
    (-2 / (k + 2)) hneg0 hneg1
  rw [spectralPower_comp A hA, spectralPower_comp C hC] at hneg
  have hAexp : (k + 2) * (-2 / (k + 2)) = -2 := by field_simp [ne_of_gt hK]
  have hCexp : s * (-2 / (k + 2)) = -2 * p / (k + p) := by
    dsimp only [s]
    field_simp [ne_of_gt hK, ne_of_gt hkp] <;> ring
  rw [hAexp, hCexp] at hneg

  -- The actual invertible polar factor has S S* = B and the stated positive Gram matrix.
  let S := fpow A (-1) * fpow C (1 / 2)
  let D := fpow C (1 / 2) * fpow A (-2) * fpow C (1 / 2)
  have hAi := spectralPower_posDef A hA (-1)
  have hCh := spectralPower_posDef C hC (1 / 2)
  have hS : IsUnit S := hAi.isUnit.mul hCh.isUnit
  have hstar : star S = fpow C (1 / 2) * fpow A (-1) := by
    dsimp only [S]
    rw [star_mul, hCh.isHermitian.star_eq, hAi.isHermitian.star_eq]
  have hSS : S * star S = B := by
    rw [hstar]
    calc
      _ = fpow A (-1) * (fpow C (1 / 2) * fpow C (1 / 2)) * fpow A (-1) := by
        dsimp only [S]
        simp only [mul_assoc]
      _ = fpow A (-1) * C * fpow A (-1) := by rw [spectralPower_half_mul_self C hC]
      _ = B := inverse_congruence_cancel A B hA
  have hAi2 : fpow A (-1) * fpow A (-1) = fpow A (-2) := by
    rw [spectralPower_mul A hA]
    norm_num
  have hGram : star S * S = D := by
    rw [hstar]
    calc
      _ = fpow C (1 / 2) * (fpow A (-1) * fpow A (-1)) * fpow C (1 / 2) := by
        dsimp only [S]
        simp only [mul_assoc]
      _ = D := by rw [hAi2]
  have hBp : fpow B p = fpow A (-1) *
      (fpow C (1 / 2) * fpow D (p - 1) * fpow C (1 / 2)) * fpow A (-1) := by
    have hpolar := spectralPower_mul_star_conjugation S hS p
    rw [hSS, hGram] at hpolar
    rw [hpolar, hstar]
    dsimp only [S]
    simp only [mul_assoc]

  -- Conjugate the negative comparison, then use the admissible power p-1 in [0,1].
  have hDle := hermitian_sandwich_order _ _ (fpow C (1 / 2)) hneg hCh.isHermitian
  rw [spectralPower_sandwich_same C hC] at hDle
  have hgamma : 2 * (1 / 2 : ℝ) + -2 * p / (k + p) = (k - p) / (k + p) := by
    field_simp [ne_of_gt hkp] <;> ring
  rw [hgamma] at hDle
  have hmono := spectralPower_order _ _ hDle (p - 1) (by linarith) (by linarith)
  rw [spectralPower_comp C hC] at hmono
  have hCbound := hermitian_sandwich_order _ _ (fpow C (1 / 2)) hmono hCh.isHermitian
  rw [spectralPower_sandwich_same C hC] at hCbound
  have hfinalExp : 2 * (1 / 2 : ℝ) + (k - p) / (k + p) * (p - 1) = s * t := by
    dsimp only [s, t]
    field_simp [ne_of_gt hK, ne_of_gt hkp] <;> ring
  rw [hfinalExp] at hCbound
  have hBbound : fpow B p ≤ fpow A (-1) * fpow C (s * t) * fpow A (-1) := by
    rw [hBp]
    exact hermitian_sandwich_order _ _ (fpow A (-1)) hCbound hAi.isHermitian

  -- The final power t is also in [0,1], so the original C^s comparison closes the bound.
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hK.le
  have ht1 : t ≤ 1 := by
    dsimp only [t]
    apply (div_le_iff₀ hK).mpr
    linarith
  have hlast := spectralPower_order _ _ hCs t ht0 ht1
  rw [spectralPower_comp C hC, spectralPower_comp A hA] at hlast
  have htExp : (k + 2) * t = k - p + 2 := by
    dsimp only [t]
    field_simp [ne_of_gt hK]
  rw [htExp] at hlast
  have hlastConj := hermitian_sandwich_order _ _ (fpow A (-1)) hlast hAi.isHermitian
  rw [spectralPower_sandwich_same A hA] at hlastConj
  have hout : 2 * (-1 : ℝ) + (k - p + 2) = k - p := by ring
  rw [hout] at hlastConj
  exact hBbound.trans hlastConj

end NLA.MI28
