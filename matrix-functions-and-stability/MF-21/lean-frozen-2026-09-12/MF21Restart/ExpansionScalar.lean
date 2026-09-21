import MF21Restart.Definitions
import MF21Restart.BulkDecay
import Mathlib.Topology.Order.LiminfLimsup

/-! Scalar and mesh estimates for assembly of (23)--(25).
The prior statement lock is EXPANSION_ASSEMBLY_STATEMENTS.md. -/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Topology

namespace MF21Restart

theorem mesh_mem_interval (n j : ℕ) (hjn : j ≤ n) :
    mesh n j ∈ Set.Icc (0 : ℝ) Real.pi := by
  have hden : 0 < (n + 2 : ℝ) := by positivity
  constructor
  · exact div_nonneg (mul_nonneg (Nat.cast_nonneg j) Real.pi_pos.le) hden.le
  · apply (div_le_iff₀ hden).mpr
    have hjnr : (j : ℝ) ≤ n := by exact_mod_cast hjn
    nlinarith [Real.pi_pos]

theorem mesh_eq_index_mul_step (n j : ℕ) :
    mesh n j = ((j : ℝ) * Real.pi) * (1 / (n + 2 : ℝ)) := by
  unfold mesh
  ring

theorem expansion_eq_sum_step (d : ℕ → ℝ → ℝ) (p n j : ℕ) :
    expansion d p n j =
      ∑ k ∈ Finset.range (p + 1), d k (mesh n j) * (1 / (n + 2 : ℝ)) ^ k := by
  unfold expansion
  simp only [div_eq_mul_inv, one_mul, inv_pow]

theorem step_pos_le_one (n : ℕ) :
    0 < 1 / (n + 2 : ℝ) ∧ 1 / (n + 2 : ℝ) ≤ 1 := by
  have hden : 0 < (n + 2 : ℝ) := by positivity
  refine ⟨one_div_pos.mpr hden, (div_le_one hden).mpr ?_⟩
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem eventually_step_le (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 / (n + 2 : ℝ) ≤ δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  refine ⟨N, ?_⟩
  intro n hn
  have hNr : (N : ℝ) ≤ n := by exact_mod_cast hn
  have ht : 1 / δ < (n + 2 : ℝ) := by linarith
  have hm := (div_lt_iff₀ hδ).mp ht
  apply (div_le_iff₀ (by positivity : 0 < (n + 2 : ℝ))).mpr
  nlinarith only [hm]

theorem nat_pow_exp_uniform_bound (q : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ M : ℝ, 0 < M ∧ ∀ j : ℕ,
      (j : ℝ) ^ q * Real.exp (-c * (j : ℝ)) ≤ M := by
  have ht : Tendsto (fun x : ℝ => x ^ q * Real.exp (-c * x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (q : ℝ) c hc
  have hnat : Tendsto (fun j : ℕ => (j : ℝ) ^ q * Real.exp (-c * (j : ℝ)))
      atTop (𝓝 0) := ht.comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := hnat.bddAbove_range
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right M 1), ?_⟩
  intro j
  exact (hM ⟨j, rfl⟩).trans (le_max_left M 1)

theorem eventually_bulk_cutoff_ge (J : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      J ≤ Nat.ceil ((Real.log (n + 2 : ℝ)) ^ 2) := by
  have hshift : Tendsto (fun n : ℕ => (n + 2 : ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop_mono
      (fun n : ℕ => show (n : ℝ) ≤ (n + 2 : ℝ) by linarith)
    exact tendsto_natCast_atTop_atTop
  have hlog := Real.tendsto_log_atTop.comp hshift
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (hlog (Filter.eventually_ge_atTop (max (J : ℝ) 1)))
  refine ⟨N, ?_⟩
  intro n hn
  have hL := hN n hn
  have hJ : (J : ℝ) ≤ Real.log (n + 2 : ℝ) := (le_max_left _ _).trans hL
  have h1 : 1 ≤ Real.log (n + 2 : ℝ) := (le_max_right _ _).trans hL
  have hsq : Real.log (n + 2 : ℝ) ≤ (Real.log (n + 2 : ℝ)) ^ 2 := by
    nlinarith
  exact_mod_cast hJ.trans (hsq.trans (Nat.le_ceil _))

/-- Vanishing of each coefficient gives the full low-index polynomial
bound at the same mesh. This contains no eigenvalue estimate. -/
theorem expansion_fixed_prefix_bound
    (m p J : ℕ) (hp : p ≤ 2 * m) (d : ℕ → ℝ → ℝ)
    (hvan : ∀ k : ℕ, k ≤ 2 * m → ∃ Ck : ℝ, 0 < Ck ∧
      ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, |d k x| ≤ Ck * x ^ (2 * m - k)) :
    ∃ B : ℝ, 0 < B ∧ ∀ n j : ℕ, j ≤ J → j ≤ n →
      |expansion d p n j| ≤ B * (1 / (n + 2 : ℝ)) ^ (2 * m) := by
  classical
  let A : ℕ → ℝ := fun k =>
    if hk : k ≤ 2 * m then Classical.choose (hvan k hk) else 1
  have hA (k : ℕ) (hk : k ≤ 2 * m) :
      0 < A k ∧ ∀ x ∈ Set.Icc (0 : ℝ) Real.pi,
        |d k x| ≤ A k * x ^ (2 * m - k) := by
    dsimp only [A]
    rw [dif_pos hk]
    exact Classical.choose_spec (hvan k hk)
  let B : ℝ := ∑ k ∈ Finset.range (p + 1), A k * ((J : ℝ) * Real.pi) ^ (2 * m - k)
  have hB : 0 ≤ B := by
    apply Finset.sum_nonneg
    intro k hk
    have hkm : k ≤ 2 * m := (Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans hp
    exact mul_nonneg (hA k hkm).1.le (pow_nonneg (by positivity) _)
  refine ⟨B + 1, by linarith, ?_⟩
  intro n j hjJ hjn
  let h : ℝ := 1 / (n + 2 : ℝ)
  have hh : 0 < h := (step_pos_le_one n).1
  have hx := mesh_mem_interval n j hjn
  have hjr : (j : ℝ) ≤ J := by exact_mod_cast hjJ
  have hterm (k : ℕ) (hk : k ∈ Finset.range (p + 1)) :
      |d k (mesh n j) * h ^ k| ≤
        (A k * ((J : ℝ) * Real.pi) ^ (2 * m - k)) * h ^ (2 * m) := by
    have hkm : k ≤ 2 * m := (Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans hp
    have hbase : (j : ℝ) * Real.pi ≤ (J : ℝ) * Real.pi :=
      mul_le_mul_of_nonneg_right hjr Real.pi_pos.le
    have hpower : ((j : ℝ) * Real.pi) ^ (2 * m - k) ≤
        ((J : ℝ) * Real.pi) ^ (2 * m - k) :=
      pow_le_pow_left₀ (by positivity) hbase _
    rw [abs_mul, abs_of_nonneg (pow_nonneg hh.le _)]
    calc
      _ ≤ (A k * (mesh n j) ^ (2 * m - k)) * h ^ k :=
        mul_le_mul_of_nonneg_right ((hA k hkm).2 _ hx) (pow_nonneg hh.le _)
      _ = (A k * ((j : ℝ) * Real.pi) ^ (2 * m - k)) * h ^ (2 * m) := by
        rw [mesh_eq_index_mul_step, mul_pow]
        change (A k * (((j : ℝ) * Real.pi) ^ (2 * m - k) * h ^ (2 * m - k))) * h ^ k = _
        calc
          _ = (A k * ((j : ℝ) * Real.pi) ^ (2 * m - k)) *
              (h ^ (2 * m - k) * h ^ k) := by ring
          _ = _ := by rw [← pow_add, Nat.sub_add_cancel hkm]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpower (hA k hkm).1.le) (pow_nonneg hh.le _)
  rw [expansion_eq_sum_step]
  change |∑ k ∈ Finset.range (p + 1), d k (mesh n j) * h ^ k| ≤ (B + 1) * h ^ (2 * m)
  calc
    _ ≤ ∑ k ∈ Finset.range (p + 1), |d k (mesh n j) * h ^ k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (p + 1),
        (A k * ((J : ℝ) * Real.pi) ^ (2 * m - k)) * h ^ (2 * m) :=
      Finset.sum_le_sum hterm
    _ = B * h ^ (2 * m) := by rw [Finset.sum_mul]
    _ ≤ (B + 1) * h ^ (2 * m) :=
      mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hh.le _)

#print axioms nat_pow_exp_uniform_bound
#print axioms eventually_bulk_cutoff_ge
#print axioms expansion_fixed_prefix_bound

end MF21Restart
