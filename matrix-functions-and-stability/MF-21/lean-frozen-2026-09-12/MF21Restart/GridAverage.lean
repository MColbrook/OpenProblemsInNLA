import MF21Restart.InverseKernelGridTop

/-! Exact right-grid averages converge to the interval integral by compact
uniform continuity. Prior lock: GRID_AVERAGE_STATEMENTS.md. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology

namespace MF21Restart

theorem continuous_grid_average_tendsto (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1)) :
    Filter.Tendsto (fun n : ℕ => (1 / (n : ℝ)) * ∑ i : Fin n, f (kernelGridPoint n i))
      Filter.atTop (𝓝 (∫ x in (0 : ℝ)..1, f x)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) (ε / 2) hhalf
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  refine ⟨max 1 N, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hnN : N ≤ n := (le_max_right _ _).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsmall : 1 / (n : ℝ) < δ := by
    have ht : 1 / δ < (n : ℝ) := hN.trans_le (by exact_mod_cast hnN)
    have hm := (div_lt_iff₀ hδ).mp ht
    apply (div_lt_iff₀ hnpos).mpr
    simpa only [mul_comm] using hm
  let q : ℕ → ℝ := fun k => (k : ℝ) / n
  have hqmono : Monotone q := by
    intro k ell hkl
    exact div_le_div_of_nonneg_right (by exact_mod_cast hkl) hnpos.le
  have hqzero : q 0 = 0 := by simp only [q, Nat.cast_zero, zero_div]
  have hqn : q n = 1 := div_self hnpos.ne'
  have hqstep (k : ℕ) : q (k + 1) - q k = 1 / (n : ℝ) := by
    dsimp only [q]
    push_cast
    ring
  have hcell (k : ℕ) (hk : k ∈ Finset.Ico 0 n) :
      Set.Icc (q k) (q (k + 1)) ⊆ Set.Icc 0 1 := by
    intro t ht
    have hk' := Finset.mem_Ico.mp hk
    constructor
    · have hq0k : 0 ≤ q k := by simpa only [hqzero] using hqmono (Nat.zero_le k)
      exact hq0k.trans ht.1
    · exact ht.2.trans (by simpa only [hqn] using hqmono (by omega : k + 1 ≤ n))
  have hfi (k : ℕ) (hk : k ∈ Finset.Ico 0 n) :
      IntervalIntegrable f MeasureTheory.volume (q k) (q (k + 1)) :=
    (hf.mono (hcell k hk)).intervalIntegrable_of_Icc (hqmono (Nat.le_succ k))
  have hosc (k : ℕ) (hk : k ∈ Finset.Ico 0 n)
      (t : ℝ) (ht : t ∈ Set.Icc (q k) (q (k + 1))) :
      |f (q (k + 1)) - f t| ≤ ε / 2 := by
    have hd : dist (q (k + 1)) t < δ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.2)]
      linarith [hqstep k, ht.1]
    have hb := hclose (q (k + 1))
      (hcell k hk ⟨hqmono (Nat.le_succ k), le_rfl⟩) t (hcell k hk ht) hd
    simpa only [Real.dist_eq] using hb.le
  have he := riemann_right_sum_error_bound q hqmono 0 n (Nat.zero_le n) f (ε / 2) hfi hosc
  have hsum : (∑ k ∈ Finset.Ico 0 n, (q (k + 1) - q k) * f (q (k + 1))) =
      (1 / (n : ℝ)) * ∑ i : Fin n, f (kernelGridPoint n i) := by
    simp_rw [hqstep]
    rw [← Finset.mul_sum, Nat.Ico_zero_eq_range]
    congr 1
    exact (Fin.sum_univ_eq_sum_range (fun k => f (((k + 1 : ℕ) : ℝ) / n)) n).symm
  rw [hsum, hqzero, hqn, sub_zero, mul_one] at he
  rw [Real.dist_eq]
  exact he.trans_lt (by linarith only [hε])

#print axioms continuous_grid_average_tendsto

end MF21Restart
