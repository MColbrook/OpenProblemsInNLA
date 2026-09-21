import MF21Restart.FixedIndex
import MF21Restart.ImplicitTaylor
import MF21Restart.ExpansionScalar

/-! The hypothetical critical UniformBound implies the literal fixed-index
limit (30) for the same actual phase and exact coefficient family.
Prior lock: ACTUAL_FIXED_INDEX_STATEMENTS.md. -/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Topology

namespace MF21Restart

/-- This covers every fixed original j>=1, including j below the tail
cutoff. The smallness of Y comes from the uniform IFT displacement. -/
theorem critical_bound_implies_actual_fixed_index_limit
    (m : ℕ) (hm : 1 ≤ m) (Y : ℝ × ℝ → ℝ)
    (r ε C δ : ℝ) (hr : 0 < r) (hε : 0 < ε) (hC : 0 < C) (hδ : 0 < δ)
    (hY : ∀ p ∈ Set.Ioo (-r / 2) (Real.pi + r / 2) ×ˢ Set.Ioo (-ε) ε,
      Y p ∈ Set.Ioo (-r) (Real.pi + r) ∧
        Y p = p.1 + p.2 * manuscriptEta m (Y p) ∧
        |Y p - p.1| ≤ C * |p.2|)
    (hTaylor : ∃ B : ℝ, 0 < B ∧
      ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, ∀ h : ℝ, |h| ≤ δ →
        |symbol m (Y (x, h)) -
            ∑ k ∈ Finset.range (2 * m + 1), implicitPhaseCoefficient m Y k x * h ^ k| ≤
          B * |h| ^ (2 * m + 1))
    (hU : UniformBound m (implicitPhaseCoefficient m Y) (2 * m)) :
    ∀ j : ℕ, 1 ≤ j →
      Tendsto (fun n : ℕ => (n + 2 : ℝ) ^ (2 * m) * eigenvalue m n j)
        atTop (𝓝 (Real.pi ^ (2 * m) *
          ((j : ℝ) + ((m - 1 : ℕ) : ℝ) / 2) ^ (2 * m))) := by
  intro j hj
  let h : ℕ → ℝ := fun n => 1 / (n + 2 : ℝ)
  let y : ℕ → ℝ := fun n => Y (mesh n j, h n)
  have hh : Tendsto h atTop (𝓝 0) := by
    simpa only [h, Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
  obtain ⟨Nε, hnε⟩ := eventually_step_le (ε / 2) (by positivity)
  obtain ⟨Nδ, hnδ⟩ := eventually_step_le δ hδ
  have hmem : ∀ᶠ n : ℕ in atTop,
      (mesh n j, h n) ∈ Set.Ioo (-r / 2) (Real.pi + r / 2) ×ˢ Set.Ioo (-ε) ε := by
    filter_upwards [eventually_ge_atTop j, eventually_ge_atTop Nε] with n hjn hn
    have hx := mesh_mem_interval n j hjn
    have hhpos : 0 < h n := (step_pos_le_one n).1
    have hhsmall : h n ≤ ε / 2 := hnε n hn
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith [hx.1, hx.2]
  have hy : Tendsto y atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun n => (C + (j : ℝ) * Real.pi) * h n)
    · filter_upwards [hmem, eventually_ge_atTop j] with n hp hjn
      have hb := (hY (mesh n j, h n) hp).2.2
      change |Y (mesh n j, h n) - mesh n j| ≤ C * |h n| at hb
      have hhpos : 0 < h n := (step_pos_le_one n).1
      have hx := mesh_mem_interval n j hjn
      rw [Real.norm_eq_abs]
      change |Y (mesh n j, h n)| ≤ _
      calc
        _ ≤ |Y (mesh n j, h n) - mesh n j| + |mesh n j| := by
          simpa only [sub_zero] using (abs_sub_le (Y (mesh n j, h n)) (mesh n j) 0)
        _ ≤ C * |h n| + |mesh n j| := add_le_add hb le_rfl
        _ = (C + (j : ℝ) * Real.pi) * h n := by
          rw [abs_of_pos hhpos, abs_of_nonneg hx.1, mesh_eq_index_mul_step]
          change C * h n + ((j : ℝ) * Real.pi) * h n = _
          ring
    · simpa only [mul_zero] using tendsto_const_nhds.mul hh
  have hEq : ∀ᶠ n : ℕ in atTop,
      y n = (Real.pi * j) * (1 / (n + 2 : ℝ)) +
        (1 / (n + 2 : ℝ)) * manuscriptEta m (y n) := by
    filter_upwards [hmem] with n hp
    have he := (hY (mesh n j, h n) hp).2.1
    change y n = mesh n j + h n * manuscriptEta m (y n) at he
    rw [mesh_eq_index_mul_step] at he
    simpa only [h, mul_comm Real.pi (j : ℝ)] using he
  obtain ⟨B, _hB, hTaylorB⟩ := hTaylor
  have hT : ∀ᶠ n : ℕ in atTop,
      |symbol m (y n) - expansion (implicitPhaseCoefficient m Y) (2 * m) n j| ≤
        B / (n + 2 : ℝ) ^ (2 * m + 1) := by
    filter_upwards [eventually_ge_atTop j, eventually_ge_atTop Nδ] with n hjn hn
    have hhpos : 0 < h n := (step_pos_le_one n).1
    have hs : |h n| ≤ δ := by rw [abs_of_pos hhpos]; exact hnδ n hn
    have ht := hTaylorB (mesh n j) (mesh_mem_interval n j hjn) (h n) hs
    rw [abs_of_pos hhpos] at ht
    rw [← expansion_eq_sum_step (implicitPhaseCoefficient m Y) (2 * m) n j] at ht
    simpa only [h, y, div_eq_mul_inv, one_mul, inv_pow] using ht
  have hEta : ContinuousAt (manuscriptEta m) 0 :=
    (manuscriptEta_contDiffAt m hm 0 ⟨le_rfl, Real.pi_pos.le⟩).continuousAt
  have hl := critical_bound_implies_fixed_index_limit m j hj hU hT hy hEta hEq
  have hvalue : (Real.pi * j + manuscriptEta m 0) ^ (2 * m) =
      Real.pi ^ (2 * m) * ((j : ℝ) + ((m - 1 : ℕ) : ℝ) / 2) ^ (2 * m) := by
    rw [manuscriptEta_zero m hm, Nat.cast_sub hm, Nat.cast_one, ← mul_pow]
    congr 1
    ring
  simpa only [hvalue] using hl

#print axioms critical_bound_implies_actual_fixed_index_limit

end MF21Restart
