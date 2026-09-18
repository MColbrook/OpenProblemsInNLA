/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

The positive-definite specialization needed from Ghabries, Abbas, Mourad and
Assi (2020), Lemma 2.3, admits a direct contraction proof. From
X Y^a X <= Y^b, put C = Y^(a/2) X Y^(a/2), so C^2 <= Y^(a+b).
Negative-power order at -a/(a+b) and positive-power order at b/(a+b) give
C Y^(-a) C <= Y^b. Conjugation back gives X^2 <= Y^(b-a).
The zero-denominator case a=b=0 is separate. Only this PD specialization is
needed by MI28; no claim about all Hermitian X is made here.

The notation fpow is the unchanged MI24 definition of the same CFC.rpow used
by MI28. No new spectral semantics or norm is introduced.
-/
import NLA.MI28.Definitions
import NLA.MI24.OrderPowers

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI28

open NLA.MI24 (spectralPower_posDef spectralPower_isHermitian spectralPower_isUnit
  posDef_hermitian_sandwich spectralPower_comp spectralPower_one spectralPower_zero
  spectralPower_mul spectralPower_mul_neg spectralPower_neg_mul
  spectralPower_sandwich_same spectralPower_order spectralPower_negative_order
  hermitian_sandwich_order)

local notation "fpow" => NLA.MI24.spectralPower

/-- The two complementary powers of a square comparison control a mixed sandwich. -/
lemma mixed_power_contraction {n : ℕ} (C Y : Mat n)
    (hC : C.PosDef) (hY : Y.PosDef) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsquare : fpow C 2 ≤ fpow Y (a + b)) :
    C * fpow Y (-a) * C ≤ fpow Y b := by
  have hCsq : fpow C 2 = C * C := by
    simpa [NLA.MI24.spectralPower, CFC.rpow_eq_pow, pow_two] using
      CFC.rpow_natCast C 2 hC.posSemidef.nonneg
  by_cases hab : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simpa only [ha0, hb0, add_zero, neg_zero, spectralPower_zero Y hY,
      hCsq, mul_one] using hsquare
  · have habpos : 0 < a + b :=
      lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hab)
    have hneg0 : -1 ≤ -a / (a + b) := by
      apply (le_div_iff₀ habpos).mpr
      linarith
    have hneg1 : -a / (a + b) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) habpos.le
    have hfrac0 : 0 ≤ b / (a + b) := div_nonneg hb habpos.le
    have hfrac1 : b / (a + b) ≤ 1 := by
      apply (div_le_iff₀ habpos).mpr
      linarith

    -- The negative power reverses the comparison and supplies the middle factor.
    have hnegative := spectralPower_negative_order (fpow C 2) (fpow Y (a + b))
      (spectralPower_posDef C hC _) (spectralPower_posDef Y hY _) hsquare
      (-a / (a + b)) hneg0 hneg1
    rw [spectralPower_comp C hC, spectralPower_comp Y hY] at hnegative
    have hnegexp : (a + b) * (-a / (a + b)) = -a := by
      field_simp [hab]
    rw [hnegexp] at hnegative
    have hconj := hermitian_sandwich_order _ _ C hnegative hC.isHermitian
    have hcollapse : C * fpow C (2 * (-a / (a + b))) * C =
        fpow C (2 * (b / (a + b))) := by
      calc
        _ = fpow C 1 * fpow C (2 * (-a / (a + b))) * fpow C 1 := by
          rw [spectralPower_one C hC]
        _ = fpow C (2 * (b / (a + b))) := by
          rw [spectralPower_sandwich_same C hC]
          congr 1
          field_simp [hab] <;> ring
    rw [hcollapse] at hconj

    -- The complementary positive power has exactly the same outer exponent.
    have hpositive := spectralPower_order _ _ hsquare (b / (a + b)) hfrac0 hfrac1
    rw [spectralPower_comp C hC, spectralPower_comp Y hY] at hpositive
    have hposexp : (a + b) * (b / (a + b)) = b := by
      field_simp [hab]
    rw [hposexp] at hpositive
    exact hconj.trans hpositive

/-- A positive matrix between opposite powers of one positive matrix contracts
its square between the corresponding difference power. -/
lemma positive_product_order {n : ℕ} (X Y : Mat n)
    (hX : X.PosDef) (hY : Y.PosDef) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : X * fpow Y a * X ≤ fpow Y b) :
    X * X ≤ fpow Y (b - a) := by
  let C := fpow Y (a / 2) * X * fpow Y (a / 2)
  have hC : C.PosDef := posDef_hermitian_sandwich _ _ hX
    (spectralPower_isHermitian Y hY _) (spectralPower_isUnit Y hY _)
  have hCsq : fpow C 2 = C * C := by
    simpa [NLA.MI24.spectralPower, CFC.rpow_eq_pow, pow_two] using
      CFC.rpow_natCast C 2 hC.posSemidef.nonneg
  have hhalf : fpow Y (a / 2) * fpow Y (a / 2) = fpow Y a := by
    rw [spectralPower_mul Y hY]
    congr 1
    ring

  -- Congruence transforms the given product comparison into a square comparison.
  have hsquare := hermitian_sandwich_order _ _ (fpow Y (a / 2)) h
    (spectralPower_isHermitian Y hY _)
  have hleft : fpow Y (a / 2) * (X * fpow Y a * X) * fpow Y (a / 2) =
      fpow C 2 := by
    rw [hCsq]
    dsimp only [C]
    rw [← hhalf]
    simp only [mul_assoc]
  have hright : fpow Y (a / 2) * fpow Y b * fpow Y (a / 2) =
      fpow Y (a + b) := by
    rw [spectralPower_sandwich_same Y hY]
    congr 1
    ring
  rw [hleft, hright] at hsquare
  have hmixed := mixed_power_contraction C Y hC hY a b ha hb hsquare

  -- Undo the congruence. The middle inverse cancels the two half powers of Y.
  have hmiddle : fpow Y (a / 2) * fpow Y (-a) * fpow Y (a / 2) = 1 := by
    rw [spectralPower_sandwich_same Y hY]
    have hexp : 2 * (a / 2) + -a = 0 := by ring
    rw [hexp, spectralPower_zero Y hY]
  have hback := hermitian_sandwich_order _ _ (fpow Y (-(a / 2))) hmixed
    (spectralPower_isHermitian Y hY _)
  have hbackleft : fpow Y (-(a / 2)) * (C * fpow Y (-a) * C) *
      fpow Y (-(a / 2)) = X * X := by
    calc
      _ = (fpow Y (-(a / 2)) * fpow Y (a / 2)) * X *
          (fpow Y (a / 2) * fpow Y (-a) * fpow Y (a / 2)) * X *
          (fpow Y (a / 2) * fpow Y (-(a / 2))) := by
        dsimp only [C]
        simp only [mul_assoc]
      _ = X * X := by
        rw [spectralPower_neg_mul Y hY, spectralPower_mul_neg Y hY, hmiddle]
        simp only [one_mul, mul_one]
  have hbackright : fpow Y (-(a / 2)) * fpow Y b * fpow Y (-(a / 2)) =
      fpow Y (b - a) := by
    rw [spectralPower_sandwich_same Y hY]
    congr 1
    ring
  rwa [hbackleft, hbackright] at hback

end NLA.MI28
