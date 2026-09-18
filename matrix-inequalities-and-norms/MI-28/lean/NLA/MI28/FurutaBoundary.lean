/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

Masatoshi Fujii, Furuta inequality and its related topics (2010), Theorem 1.3,
printed p. 30: extend the base interval by replacing X with X^(1+u) and
Y with (X^(u/2) Y^a X^(u/2))^((1+u)/(a+u)). The base theorem then reaches
every r in [u, 1+2u]. Induction on a natural upper bound covers all real r >= 0.
This is symbolic induction, with no numerical sampling of parameters.

The seven imported MI24 sources are reused unchanged; see REUSE-MI24-FURUTA.json.
Their spectralPower and the frozen MI28 spectralPower both denote CFC.rpow.
The final simpa exposes those definitions only at the contract boundary.
-/
import NLA.MI28.Definitions
import NLA.MI24.FurutaBase
import Mathlib.Algebra.Order.Archimedean.Basic

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI28

open NLA.MI24 (spectralPower_posDef spectralPower_isHermitian spectralPower_isUnit
  posDef_hermitian_sandwich spectralPower_comp spectralPower_one spectralPower_mul)

local notation "fpow" => NLA.MI24.spectralPower

/-- A boundary comparison at u extends to the full interval [u, 1+2u]. -/
lemma furuta_boundary_step {n : ℕ} (X Y : Mat n)
    (hX : X.PosDef) (hY : Y.PosDef) (a u r : ℝ)
    (ha : 1 ≤ a) (hu : 0 ≤ u) (hur : u ≤ r) (hr : r ≤ 1 + 2 * u)
    (hboundary : fpow (fpow X (u / 2) * fpow Y a * fpow X (u / 2))
      ((1 + u) / (a + u)) ≤ fpow X (1 + u)) :
    fpow (fpow X (r / 2) * fpow Y a * fpow X (r / 2))
      ((1 + r) / (a + r)) ≤ fpow X (1 + r) := by
  let X₁ := fpow X (1 + u)
  let D := fpow X (u / 2) * fpow Y a * fpow X (u / 2)
  let Y₁ := fpow D ((1 + u) / (a + u))
  let s := (a + u) / (1 + u)
  let t := (r - u) / (1 + u)
  have hden₁ : 0 < 1 + u := by linarith
  have hden₂ : 0 < a + u := by linarith
  have hdenr : 0 < a + r := by linarith
  have hs : 1 ≤ s := by
    dsimp only [s]
    apply (le_div_iff₀ hden₁).mpr
    linarith
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hur) hden₁.le
  have ht1 : t ≤ 1 := by
    dsimp only [t]
    apply (div_le_iff₀ hden₁).mpr
    linarith

  -- Positive definiteness justifies power composition for every real exponent.
  have hX₁ : X₁.PosDef := spectralPower_posDef X hX _
  have hD : D.PosDef := posDef_hermitian_sandwich _ _
    (spectralPower_posDef Y hY _) (spectralPower_isHermitian X hX _)
    (spectralPower_isUnit X hX _)
  have hY₁ : Y₁.PosDef := spectralPower_posDef D hD _
  have hY₁X₁ : Y₁ ≤ X₁ := hboundary

  -- The reciprocal exponent s recovers the original positive sandwich D.
  have hYpow : fpow Y₁ s = D := by
    dsimp only [Y₁, s]
    rw [spectralPower_comp D hD]
    have hcancel : (1 + u) / (a + u) * ((a + u) / (1 + u)) = 1 := by
      field_simp [ne_of_gt hden₁, ne_of_gt hden₂] <;> ring
    rw [hcancel, spectralPower_one D hD]
  have hXpow : fpow X₁ (t / 2) = fpow X ((r - u) / 2) := by
    dsimp only [X₁, t]
    rw [spectralPower_comp X hX]
    congr 1
    field_simp [ne_of_gt hden₁] <;> ring
  have hleft : (r - u) / 2 + u / 2 = r / 2 := by ring
  have hright : u / 2 + (r - u) / 2 = r / 2 := by ring
  have hinner : fpow X₁ (t / 2) * fpow Y₁ s * fpow X₁ (t / 2) =
      fpow X (r / 2) * fpow Y a * fpow X (r / 2) := by
    rw [hXpow, hYpow]
    calc
      fpow X ((r - u) / 2) * D * fpow X ((r - u) / 2) =
          (fpow X ((r - u) / 2) * fpow X (u / 2)) * fpow Y a *
            (fpow X (u / 2) * fpow X ((r - u) / 2)) := by
        dsimp only [D]
        simp only [mul_assoc]
      _ = fpow X (r / 2) * fpow Y a * fpow X (r / 2) := by
        rw [spectralPower_mul X hX, spectralPower_mul X hX, hleft, hright]

  -- Both the outer power and its denominator transform to the boundary at r.
  have hout : fpow X₁ (1 + t) = fpow X (1 + r) := by
    dsimp only [X₁]
    rw [spectralPower_comp X hX]
    congr 1
    dsimp only [t]
    field_simp [ne_of_gt hden₁] <;> ring
  have hst : 0 < s + t := by linarith
  have hexp : (1 + t) / (s + t) = (1 + r) / (a + r) := by
    apply (div_eq_div_iff (ne_of_gt hst) (ne_of_gt hdenr)).mpr
    dsimp only [s, t]
    field_simp [ne_of_gt hden₁] <;> ring
  have h := NLA.MI24.furuta_base X₁ Y₁ hX₁ hY₁ hY₁X₁ s t hs ht0 ht1
  rwa [hinner, hout, hexp] at h

private lemma furuta_boundary_le_nat {n : ℕ} (X Y : Mat n)
    (hX : X.PosDef) (hY : Y.PosDef) (hYX : Y ≤ X)
    (a : ℝ) (ha : 1 ≤ a) (N : ℕ) :
    ∀ r : ℝ, 0 ≤ r → r ≤ (N : ℝ) →
      fpow (fpow X (r / 2) * fpow Y a * fpow X (r / 2))
        ((1 + r) / (a + r)) ≤ fpow X (1 + r) := by
  induction N with
  | zero =>
      intro r hr hrN
      have hr1 : r ≤ 1 := by
        simp only [Nat.cast_zero] at hrN
        linarith
      exact NLA.MI24.furuta_base X Y hX hY hYX a r ha hr hr1
  | succ N ih =>
      intro r hr hrN
      by_cases hprev : r ≤ (N : ℝ)
      · exact ih r hr hprev
      · have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
        have hNr : (N : ℝ) ≤ r := le_of_lt (lt_of_not_ge hprev)
        have hupper : r ≤ (N : ℝ) + 1 := by
          simpa only [Nat.cast_succ] using hrN
        have hreach : r ≤ 1 + 2 * (N : ℝ) := by linarith
        exact furuta_boundary_step X Y hX hY a (N : ℝ) r ha hN0 hNr hreach
          (ih (N : ℝ) hN0 le_rfl)

/-- C05: Fujii's symbolic extension covers every nonnegative sandwich parameter. -/
theorem furuta_boundary {n : ℕ} (X Y : Mat n)
    (hX : X.PosDef) (hY : Y.PosDef) (hYX : Y ≤ X)
    (a r : ℝ) (ha : 1 ≤ a) (hr : 0 ≤ r) :
    spectralPower (spectralPower X (r / 2) * spectralPower Y a *
      spectralPower X (r / 2)) ((1 + r) / (a + r)) ≤
        spectralPower X (1 + r) := by
  obtain ⟨N, hN⟩ := exists_nat_ge r
  -- The two project definitions use the same complex-matrix CFC real power.
  simpa only [spectralPower, NLA.MI24.spectralPower] using
    furuta_boundary_le_nat X Y hX hY hYX a ha N r hr hN

end NLA.MI28
