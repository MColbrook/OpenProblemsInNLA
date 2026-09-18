/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

The positive-parameter norm lemmas cover the full interior. At p=0 the two
normalized matrices are equal. At k=0 and p>0 the sequence k_m=1/(m+1)
lies in the proved small-base range; C14 and the closed real order pass its
inequality to the limit. This is an exact limit argument, not a parameter grid.
-/
import NLA.MI28.SmallBaseNorm
import NLA.MI28.LargeBaseNorm
import NLA.MI28.NormalizedContinuity
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Topology
noncomputable section
namespace NLA.MI28

lemma normalized_zero_power {n : ℕ} (A B : Mat n) (hA : A.PosDef) (hB : B.PosDef)
    (k : ℝ) : normalizedH A B k 0 = normalizedZ A B k 0 := by
  have hM := matrixModulus_posDef (A * B) (hA.isUnit.mul hB.isUnit)
  have hBzero : spectralPower B 0 = 1 := NLA.MI24.spectralPower_zero B hB
  have hMzero : spectralPower (matrixModulus (A * B)) 0 = 1 :=
    NLA.MI24.spectralPower_zero _ hM
  simp only [normalizedH, normalizedZ, hBzero, hMzero, zero_sub]

lemma zero_base_norm {n : ℕ} (hn : 1 ≤ n) (A B : Mat n) (hA : A.PosDef)
    (hB : B.PosDef) (p : ℝ) (hp0 : 0 < p) (hp2 : p ≤ 2) :
    operatorNorm (normalizedH A B 0 p) ≤ operatorNorm (normalizedZ A B 0 p) := by
  have hc := normalized_norm_continuous A B hA hB p
  have hseq := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  apply le_of_tendsto_of_tendsto' ((hc.1.tendsto 0).comp hseq)
    ((hc.2.tendsto 0).comp hseq)
  intro m
  have hden : 0 < (m : ℝ) + 1 := by positivity
  have hk0 : 0 < 1 / ((m : ℝ) + 1) := one_div_pos.mpr hden
  have hk2 : 1 / ((m : ℝ) + 1) ≤ 2 := by
    apply (div_le_iff₀ hden).mpr
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  exact small_base_norm hn A B hA hB _ p hk0 hk2 hp0 hp2

/-- The literal norm comparison for every k>=0 and every p in the closed interval [0,2]. -/
lemma full_normalized_norm {n : ℕ} (hn : 1 ≤ n) (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (k p : ℝ) (hk0 : 0 ≤ k)
    (hp0 : 0 ≤ p) (hp2 : p ≤ 2) :
    operatorNorm (normalizedH A B k p) ≤ operatorNorm (normalizedZ A B k p) := by
  rcases hp0.eq_or_lt with hp | hp
  · subst p
    rw [normalized_zero_power A B hA hB]
  rcases hk0.eq_or_lt with hk | hk
  · subst k
    exact zero_base_norm hn A B hA hB p hp hp2
  by_cases hk2 : k ≤ 2
  · exact small_base_norm hn A B hA hB k p hk hk2 hp hp2
  · exact large_base_norm hn A B hA hB k p (lt_of_not_ge hk2).le hp hp2

end NLA.MI28
