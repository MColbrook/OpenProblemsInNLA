/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

The parameter-swap identity in George Stepaniants's canonical MI28 solution
keeps the factor order M^(-1) B, where M=|AB|. C02 gives M^2=B A^2 B.
Inverse congruence gives B M^(-2) B=A^(-2); equality of positive square roots
then gives |M^(-1) B|=A^(-1). C02 retains the actual C01 certificate dependency.
-/
import NLA.MI28.ModulusPowers
import NLA.MI28.NormalizedPositivity
import NLA.MI28.InverseSandwich

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI28

open NLA.MI24 (spectralPower_posDef spectralPower_comp spectralPower_one
  spectralPower_mul_neg spectralPower_neg_mul)

local notation "fpow" => NLA.MI24.spectralPower

/-- C03: the canonical parameter-swap modulus, with the exact factor order. -/
theorem swapped_modulus {n : ℕ} (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) :
    matrixModulus (spectralPower (matrixModulus (A * B)) (-1) * B) =
      spectralPower A (-1) := by
  let M := matrixModulus (A * B)
  have hM : M.PosDef := matrixModulus_posDef _ (hA.isUnit.mul hB.isUnit)
  have hM2 : fpow M 2 = B * fpow A 2 * B := by
    -- The selected square identity uses the same CFC powers as the reused API.
    simpa only [M, spectralPower, NLA.MI24.spectralPower] using
      product_modulus_square A B hA hB

  -- Invert the concrete positive sandwich, then compose its inner square power.
  have hMneg : fpow M (-2) = fpow B (-1) * fpow A (-2) * fpow B (-1) := by
    calc
      fpow M (-2) = fpow (fpow M 2) (-1) := by
        rw [spectralPower_comp M hM]
        norm_num
      _ = fpow (B * fpow A 2 * B) (-1) := by rw [hM2]
      _ = fpow B (-1) * fpow (fpow A 2) (-1) * fpow B (-1) :=
        power_inverse_sandwich _ B (spectralPower_posDef A hA _) hB
      _ = fpow B (-1) * fpow A (-2) * fpow B (-1) := by
        rw [spectralPower_comp A hA]
        norm_num
  have hBleft : B * fpow B (-1) = 1 := by
    simpa only [spectralPower_one B hB] using spectralPower_mul_neg B hB 1
  have hBright : fpow B (-1) * B = 1 := by
    simpa only [spectralPower_one B hB] using spectralPower_neg_mul B hB 1
  have hcancel : B * fpow M (-2) * B = fpow A (-2) := by
    rw [hMneg]
    calc
      B * (fpow B (-1) * fpow A (-2) * fpow B (-1)) * B =
          (B * fpow B (-1)) * fpow A (-2) * (fpow B (-1) * B) := by
        simp only [mul_assoc]
      _ = fpow A (-2) := by rw [hBleft, hBright]; simp only [one_mul, mul_one]

  -- Apply C02 to the new positive pair and identify its modulus square.
  let W := fpow M (-1) * B
  have hMi : (fpow M (-1)).PosDef := spectralPower_posDef M hM _
  have hW : (matrixModulus W).PosDef := matrixModulus_posDef _ (hMi.isUnit.mul hB.isUnit)
  have hW2 : fpow (matrixModulus W) 2 = B * fpow (fpow M (-1)) 2 * B := by
    simpa only [W, spectralPower, NLA.MI24.spectralPower] using
      product_modulus_square (fpow M (-1)) B hMi hB
  rw [spectralPower_comp M hM] at hW2
  have hnegTwo : (-1 : ℝ) * 2 = -2 := by norm_num
  rw [hnegTwo, hcancel] at hW2

  -- Positive definiteness makes the half powers undo the squares on both sides.
  have hroot := congrArg (fun T : Mat n => fpow T (1 / 2)) hW2
  rw [spectralPower_comp _ hW, spectralPower_comp A hA] at hroot
  have htwoHalf : (2 : ℝ) * (1 / 2) = 1 := by norm_num
  have hnegHalf : (-2 : ℝ) * (1 / 2) = -1 := by norm_num
  rw [htwoHalf, hnegHalf, spectralPower_one _ hW] at hroot
  simpa only [W, M, spectralPower, NLA.MI24.spectralPower] using hroot

#print axioms swapped_modulus
#assert_trust kernel swapped_modulus

end NLA.MI28
