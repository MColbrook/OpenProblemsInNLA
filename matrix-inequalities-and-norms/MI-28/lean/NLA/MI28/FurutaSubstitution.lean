/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

Shared substitution in the two Furuta arguments of the canonical MI28 solution:
X=A^k, Y=|AB|^p, a=2/p and r=2/k. The concrete inner sandwich is (ABA)^2.
No upper bound on r is imposed; the proved C06 is used at its full real range.
-/
import NLA.MI28.FurutaAdmissible
import NLA.MI28.ModulusPowers
import NLA.MI28.NormalizedPositivity

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI28

open NLA.MI24 (spectralPower_posDef spectralPower_comp spectralPower_one
  spectralPower_mul_neg spectralPower_neg_mul posDef_hermitian_sandwich)

local notation "fpow" => NLA.MI24.spectralPower

lemma inverse_congruence_cancel {n : ℕ} (A B : Mat n) (hA : A.PosDef) :
    fpow A (-1) * (A * B * A) * fpow A (-1) = B := by
  have hleft : fpow A (-1) * A = 1 := by
    simpa only [spectralPower_one A hA] using spectralPower_neg_mul A hA 1
  have hright : A * fpow A (-1) = 1 := by
    simpa only [spectralPower_one A hA] using spectralPower_mul_neg A hA 1
  calc
    _ = (fpow A (-1) * A) * B * (A * fpow A (-1)) := by simp only [mul_assoc]
    _ = B := by rw [hleft, hright]; simp only [one_mul, mul_one]

lemma sandwich_square {n : ℕ} (A B : Mat n) (hA : A.PosDef) (hB : B.PosDef) :
    fpow (A * B * A) 2 = A * (B * fpow A 2 * B) * A := by
  have hC := posDef_hermitian_sandwich B A hB hA.isHermitian hA.isUnit
  have hC2 : fpow (A * B * A) 2 = (A * B * A) * (A * B * A) := by
    simpa [NLA.MI24.spectralPower, CFC.rpow_eq_pow, pow_two] using
      CFC.rpow_natCast (A * B * A) 2 hC.posSemidef.nonneg
  have hA2 : fpow A 2 = A * A := by
    simpa [NLA.MI24.spectralPower, CFC.rpow_eq_pow, pow_two] using
      CFC.rpow_natCast A 2 hA.posSemidef.nonneg
  rw [hC2, hA2]
  simp only [mul_assoc]

/-- The common concrete consequence of C06, before either parameter choice for q. -/
lemma furuta_square_order {n : ℕ} (A B : Mat n) (hA : A.PosDef) (hB : B.PosDef)
    (k p q : ℝ) (hk : 0 < k) (hp : 0 < p) (hp2 : p ≤ 2) (hq : 1 ≤ q)
    (hadm : 2 / p + 2 / k ≤ (1 + 2 / k) * q)
    (h : fpow (matrixModulus (A * B)) p ≤ fpow A k) :
    fpow (A * B * A) (2 / q) ≤ fpow A ((2 * k / p + 2) / q) := by
  let M := matrixModulus (A * B)
  let C := A * B * A
  have hM : M.PosDef := matrixModulus_posDef _ (hA.isUnit.mul hB.isUnit)
  have hC : C.PosDef := posDef_hermitian_sandwich B A hB hA.isHermitian hA.isUnit
  have ha : 1 ≤ 2 / p := by
    apply (le_div_iff₀ hp).mpr
    simpa only [one_mul] using hp2
  have hr : 0 ≤ 2 / k := div_nonneg (by norm_num) hk.le
  have hq0 : 0 < q := by linarith

  -- Recover A and M^2 from the two nested powers in the Furuta sandwich.
  have hApow : fpow (fpow A k) ((2 / k) / 2) = A := by
    rw [spectralPower_comp A hA]
    have hexp : k * ((2 / k) / 2) = 1 := by field_simp [ne_of_gt hk]
    rw [hexp, spectralPower_one A hA]
  have hMpow : fpow (fpow M p) (2 / p) = fpow M 2 := by
    rw [spectralPower_comp M hM]
    congr 1
    field_simp [ne_of_gt hp]
  have hM2 : fpow M 2 = B * fpow A 2 * B := by
    simpa only [M, spectralPower, NLA.MI24.spectralPower] using
      product_modulus_square A B hA hB
  have hinner : fpow (fpow A k) ((2 / k) / 2) * fpow (fpow M p) (2 / p) *
      fpow (fpow A k) ((2 / k) / 2) = fpow C 2 := by
    rw [hApow, hMpow, hM2]
    exact (sandwich_square A B hA hB).symm

  -- Apply the exact selected C06 and translate its identical CFC wrappers once.
  have hF : fpow (fpow (fpow A k) ((2 / k) / 2) * fpow (fpow M p) (2 / p) *
      fpow (fpow A k) ((2 / k) / 2)) (1 / q) ≤
      fpow (fpow A k) ((2 / p + 2 / k) / q) := by
    simpa only [spectralPower, NLA.MI24.spectralPower] using
      furuta_admissible (fpow A k) (fpow M p)
        (spectralPower_posDef A hA _) (spectralPower_posDef M hM _) h
        (2 / p) (2 / k) q ha hr hq hadm
  rw [hinner, spectralPower_comp C hC, spectralPower_comp A hA] at hF
  have hleft : 2 * (1 / q) = 2 / q := by ring
  have hright : k * ((2 / p + 2 / k) / q) = (2 * k / p + 2) / q := by
    field_simp [ne_of_gt hk, ne_of_gt hp, ne_of_gt hq0] <;> ring
  rwa [hleft, hright] at hF

end NLA.MI28
