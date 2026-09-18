/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

Conjugating by inverse powers of one positive matrix translates both normalized
contractions into the exact premise and conclusion of frozen OrderImplication.
The middle matrix is arbitrary; no additional spectral or sign premise is used.
-/
import NLA.MI28.Definitions
import NLA.MI24.OrderPowers

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI28

open NLA.MI24 (spectralPower_isHermitian spectralPower_mul spectralPower_zero
  spectralPower_mul_neg spectralPower_neg_mul spectralPower_sandwich_same
  hermitian_sandwich_order)

local notation "fpow" => NLA.MI24.spectralPower

lemma power_sandwich_le_one_iff {n : ℕ} (A M : Mat n) (hA : A.PosDef) (r : ℝ) :
    fpow A r * M * fpow A r ≤ 1 ↔ M ≤ fpow A (-2 * r) := by
  constructor
  · intro h
    have hconj := hermitian_sandwich_order _ _ (fpow A (-r)) h
      (spectralPower_isHermitian A hA _)
    calc
      M = (fpow A (-r) * fpow A r) * M * (fpow A r * fpow A (-r)) := by
        rw [spectralPower_neg_mul A hA, spectralPower_mul_neg A hA]
        simp only [one_mul, mul_one]
      _ = fpow A (-r) * (fpow A r * M * fpow A r) * fpow A (-r) := by
        simp only [mul_assoc]
      _ ≤ fpow A (-r) * 1 * fpow A (-r) := hconj
      _ = fpow A (-2 * r) := by
        rw [mul_one, spectralPower_mul A hA]
        congr 1
        ring
  · intro h
    have hconj := hermitian_sandwich_order _ _ (fpow A r) h
      (spectralPower_isHermitian A hA _)
    calc
      fpow A r * M * fpow A r ≤ fpow A r * fpow A (-2 * r) * fpow A r := hconj
      _ = 1 := by
        rw [spectralPower_sandwich_same A hA]
        have hexp : 2 * r + -2 * r = 0 := by ring
        rw [hexp, spectralPower_zero A hA]

lemma normalizedZ_le_one_iff {n : ℕ} (A B : Mat n) (hA : A.PosDef) (k p : ℝ) :
    normalizedZ A B k p ≤ 1 ↔
      spectralPower (matrixModulus (A * B)) p ≤ spectralPower A k := by
  have h := power_sandwich_le_one_iff A (spectralPower (matrixModulus (A * B)) p)
    hA (-k / 2)
  have hexp : -2 * (-k / 2) = k := by ring
  -- Both power wrappers reduce to the same CFC.rpow; only the exponent is normalized.
  simpa only [normalizedZ, spectralPower, NLA.MI24.spectralPower, hexp] using h

lemma normalizedH_le_one_iff {n : ℕ} (A B : Mat n) (hA : A.PosDef) (k p : ℝ) :
    normalizedH A B k p ≤ 1 ↔ spectralPower B p ≤ spectralPower A (k - p) := by
  have h := power_sandwich_le_one_iff A (spectralPower B p) hA ((p - k) / 2)
  have hexp : -2 * ((p - k) / 2) = k - p := by ring
  simpa only [normalizedH, spectralPower, NLA.MI24.spectralPower, hexp] using h

end NLA.MI28
