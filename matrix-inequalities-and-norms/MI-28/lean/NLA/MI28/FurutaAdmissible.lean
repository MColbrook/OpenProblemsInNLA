/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

The admissible form follows from the unbounded boundary theorem by a single
Loewner-Heinz power (a+r)/((1+r)q). Its membership in [0,1] is a consequence
of the exact Furuta admissibility hypothesis, without parameter truncation.
-/
import NLA.MI28.FurutaBoundary

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI28

open NLA.MI24 (spectralPower_posDef spectralPower_isHermitian spectralPower_isUnit
  posDef_hermitian_sandwich spectralPower_comp spectralPower_order)

local notation "fpow" => NLA.MI24.spectralPower

/-- C06: the full admissible Furuta range follows by operator-monotone powering. -/
theorem furuta_admissible {n : ℕ} (X Y : Mat n)
    (hX : X.PosDef) (hY : Y.PosDef) (hYX : Y ≤ X)
    (a r q : ℝ) (ha : 1 ≤ a) (hr : 0 ≤ r) (hq : 1 ≤ q)
    (hadm : a + r ≤ (1 + r) * q) :
    spectralPower (spectralPower X (r / 2) * spectralPower Y a *
      spectralPower X (r / 2)) (1 / q) ≤
        spectralPower X ((a + r) / q) := by
  let D := fpow X (r / 2) * fpow Y a * fpow X (r / 2)
  let s := (a + r) / ((1 + r) * q)
  have hden₁ : 0 < 1 + r := by linarith
  have hden₂ : 0 < a + r := by linarith
  have hq0 : 0 < q := by linarith
  have hden : 0 < (1 + r) * q := mul_pos hden₁ hq0
  have hs0 : 0 ≤ s := div_nonneg hden₂.le hden.le
  have hs1 : s ≤ 1 := by
    dsimp only [s]
    apply (div_le_iff₀ hden).mpr
    simpa only [one_mul] using hadm
  have hD : D.PosDef := posDef_hermitian_sandwich _ _
    (spectralPower_posDef Y hY _) (spectralPower_isHermitian X hX _)
    (spectralPower_isUnit X hX _)
  have hbase : fpow D ((1 + r) / (a + r)) ≤ fpow X (1 + r) := by
    -- Reuse the selected C05 theorem through the identical CFC definitions.
    simpa only [D, spectralPower, NLA.MI24.spectralPower] using
      furuta_boundary X Y hX hY hYX a r ha hr
  have h := spectralPower_order _ _ hbase s hs0 hs1
  rw [spectralPower_comp D hD, spectralPower_comp X hX] at h
  have hin : (1 + r) / (a + r) * s = 1 / q := by
    dsimp only [s]
    field_simp [ne_of_gt hden₁, ne_of_gt hden₂, ne_of_gt hq0] <;> ring
  have hout : (1 + r) * s = (a + r) / q := by
    dsimp only [s]
    field_simp [ne_of_gt hden₁, ne_of_gt hq0] <;> ring
  rw [hin, hout] at h
  -- Return to the frozen MI28 spelling of the same concrete matrix powers.
  simpa only [D, spectralPower, NLA.MI24.spectralPower] using h

end NLA.MI28
