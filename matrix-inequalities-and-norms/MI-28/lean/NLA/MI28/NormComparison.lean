/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

One positive scalar normalization converts any proved OrderImplication into
the concrete Euclidean operator-norm comparison. Both C11 and C12 can consume
this lemma. The norm/order method follows MI24 HeronNorm, authored by George
Stepaniants with Codex agent /root/nm04_final_referee1; its problem-specific
Heron modules are not imported. The exact norm bridge is reused from Mathlib.
-/
import NLA.MI28.NormalizedPositivity
import NLA.MI28.NormalizedHomogeneity
import NLA.MI28.NormalizedOrder

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI28

private lemma operatorNorm_eq_l2 {n : ℕ} (A : Mat n) : operatorNorm A = ‖A‖ :=
  Matrix.l2_opNorm_toEuclideanCLM A

private lemma operatorNorm_pos {n : ℕ} (hn : 1 ≤ n) (A : Mat n)
    (hA : A.PosDef) : 0 < operatorNorm A := by
  let : NeZero n := ⟨by omega⟩
  rw [operatorNorm_eq_l2]
  exact norm_pos_iff.mpr hA.isUnit.ne_zero

private lemma operatorNorm_smul_pos {n : ℕ} (A : Mat n) (c : ℝ) (hc : 0 < c) :
    operatorNorm ((c : ℂ) • A) = c * operatorNorm A := by
  simp only [operatorNorm_eq_l2, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hc]

/-- A universal order implication yields the actual normalized Euclidean norms. -/
lemma norm_comparison_of_order_implication (k p : ℝ) (hp : 0 < p)
    (himp : OrderImplication k p) {n : ℕ} (hn : 1 ≤ n) (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) :
    operatorNorm (normalizedH A B k p) ≤ operatorNorm (normalizedZ A B k p) := by
  let c := operatorNorm (normalizedZ A B k p)
  have hc : 0 < c := operatorNorm_pos hn _ (normalized_posdef A B hA hB k p).2
  let d := c ^ (-1 / p)
  have hd : 0 < d := Real.rpow_pos_of_pos hc _
  have hdPower : Real.rpow d p = c⁻¹ := by
    dsimp only [d]
    -- Real.rpow_mul uses real-power notation, whereas C13 names Real.rpow explicitly.
    rw [Real.rpow_eq_pow, ← Real.rpow_mul hc.le]
    have hexp : (-1 / p) * p = -1 := by field_simp [ne_of_gt hp]
    rw [hexp, Real.rpow_neg_one]
  let B' := (d : ℂ) • B
  have hB' : B'.PosDef := hB.smul (by exact_mod_cast hd)
  have hhom := normalized_homogeneity A B hA hB k p d hd

  -- Scaling makes the positive target a contraction in the concrete operator norm.
  have hZnorm : operatorNorm (normalizedZ A B' k p) = 1 := by
    dsimp only [B']
    rw [hhom.2, hdPower, operatorNorm_smul_pos _ (c⁻¹) (inv_pos.mpr hc)]
    exact inv_mul_cancel₀ (ne_of_gt hc)
  have hZ : normalizedZ A B' k p ≤ 1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _
      (normalized_posdef A B' hA hB' k p).2.posSemidef.nonneg).mp
    rw [← operatorNorm_eq_l2, hZnorm]

  -- The two congruence equivalences identify exactly the frozen implication.
  have hH : normalizedH A B' k p ≤ 1 := by
    apply (normalizedH_le_one_iff A B' hA k p).mpr
    exact himp n hn A B' hA hB' ((normalizedZ_le_one_iff A B' hA k p).mp hZ)
  have hHnorm : operatorNorm (normalizedH A B' k p) ≤ 1 := by
    rw [operatorNorm_eq_l2]
    exact (CStarAlgebra.norm_le_one_iff_of_nonneg _
      (normalized_posdef A B' hA hB' k p).1.posSemidef.nonneg).mpr hH

  -- Undo the same positive scaling on the source; c is the original target norm.
  dsimp only [B'] at hHnorm
  rw [hhom.1, hdPower, operatorNorm_smul_pos _ (c⁻¹) (inv_pos.mpr hc)] at hHnorm
  have hmul := mul_le_mul_of_nonneg_left hHnorm hc.le
  simpa only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc), one_mul, mul_one] using hmul

end NLA.MI28
