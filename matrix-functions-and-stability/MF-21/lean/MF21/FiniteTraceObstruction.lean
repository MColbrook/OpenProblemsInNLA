import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Data.Finset.Lattice.Fold

/-!
The compactness step behind Section 5, Corollary 6. A distinct trace limit,
together with a uniform summable bound outside the first coordinate, forces
an eventual discrepancy in a fixed finite set of coordinates. These are
reusable analytic lemmas: their hypotheses still have to be established for
the actual Toeplitz eigenvalues.
-/

open Filter Finset
open scoped Topology

namespace MF21Audit

theorem finite_head_separation_of_trace
    (x : ℕ → ℕ → ℝ) (v g : ℕ → ℝ) (A : ℝ)
    (hx : ∀ n, Summable (x n)) (hv : Summable v) (hg : Summable g)
    (hbound : ∀ n j, 1 ≤ j → |x n j| ≤ g j)
    (htrace : Tendsto (fun n ↦ ∑' j, x n j) atTop (𝓝 A))
    (hne : A ≠ ∑' j, v j) :
    ∃ J : ℕ, 0 < J ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ n in atTop, ∃ j < J, ε < |x n j - v j| := by
  let D := |A - ∑' j, v j|
  have hD : 0 < D := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨G, hG⟩ := Metric.tendsto_atTop.mp (tendsto_sum_nat_add g)
    (D / 8) (by positivity)
  obtain ⟨V, hV⟩ := Metric.tendsto_atTop.mp (tendsto_sum_nat_add v)
    (D / 8) (by positivity)
  let J := max 1 (max G V)
  have hJ : 0 < J := lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)
  have hJG : G ≤ J := (le_max_left G V).trans (le_max_right _ _)
  have hJV : V ≤ J := (le_max_right G V).trans (le_max_right _ _)
  have htG : |∑' j, g (j + J)| < D / 8 := by
    simpa only [Real.dist_eq, sub_zero] using hG J hJG
  have htV : |∑' j, v (j + J)| < D / 8 := by
    simpa only [Real.dist_eq, sub_zero] using hV J hJV
  have htX (n : ℕ) : |∑' j, x n (j + J)| < D / 8 := by
    have h := tsum_of_norm_bounded ((summable_nat_add_iff J).mpr hg).hasSum
      (fun j ↦ (show ‖x n (j + J)‖ ≤ g (j + J) by
        rw [Real.norm_eq_abs]
        exact hbound n (j + J) (by omega)))
    rw [Real.norm_eq_abs] at h
    exact h.trans_lt ((le_abs_self _).trans_lt htG)
  refine ⟨J, hJ, D / (8 * J), by positivity, ?_⟩
  have hevent := Metric.tendsto_nhds.mp htrace (D / 8) (by positivity)
  filter_upwards [hevent] with n hn
  rw [Real.dist_eq, abs_sub_comm] at hn
  by_contra h
  push Not at h
  have hhead : |(∑ j ∈ range J, x n j) - ∑ j ∈ range J, v j| ≤ D / 8 := by
    rw [← sum_sub_distrib]
    calc
      |∑ j ∈ range J, (x n j - v j)| ≤ ∑ j ∈ range J, |x n j - v j| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ range J, D / (8 * J) :=
        sum_le_sum (fun j hj ↦ h j (mem_range.mp hj))
      _ = D / 8 := by
        simp only [sum_const, card_range, nsmul_eq_mul]
        have hj : (J : ℝ) ≠ 0 := by positivity
        field_simp
  have hdecomp : A - ∑' j, v j =
      (A - ∑' j, x n j) +
      ((∑ j ∈ range J, x n j) - ∑ j ∈ range J, v j) +
      (∑' j, x n (j + J)) - ∑' j, v (j + J) := by
    have hx' := (hx n).sum_add_tsum_nat_add J
    have hv' := hv.sum_add_tsum_nat_add J
    linarith
  have htri : D ≤ |A - ∑' j, x n j| +
      |(∑ j ∈ range J, x n j) - ∑ j ∈ range J, v j| +
      |∑' j, x n (j + J)| + |∑' j, v (j + J)| := by
    dsimp only [D]
    rw [hdecomp]
    calc
      _ ≤ |(A - ∑' j, x n j) +
          ((∑ j ∈ range J, x n j) - ∑ j ∈ range J, v j) +
          ∑' j, x n (j + J)| + |∑' j, v (j + J)| := abs_sub _ _
      _ ≤ _ := by gcongr; exact (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
  have hxn := htX n
  linarith

theorem finite_head_separation_of_inverse_trace
    (x q : ℕ → ℕ → ℝ) (b g : ℕ → ℝ) (A : ℝ)
    (hx : ∀ n, Summable (x n))
    (hb : ∀ j, 0 < b j) (hv : Summable (fun j ↦ (b j)⁻¹)) (hg : Summable g)
    (hlink : ∀ n j, j < n → x n j = (q n j)⁻¹)
    (hbound : ∀ n j, 1 ≤ j → |x n j| ≤ g j)
    (htrace : Tendsto (fun n ↦ ∑' j, x n j) atTop (𝓝 A))
    (hne : A ≠ ∑' j, (b j)⁻¹) :
    ∃ J : ℕ, 0 < J ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ n in atTop, ∃ j < J, ε < |q n j - b j| := by
  obtain ⟨J, hJ, e, he, hsep⟩ :=
    finite_head_separation_of_trace x (fun j ↦ (b j)⁻¹) g A hx hv hg hbound htrace hne
  have hlocal (j : ℕ) : ∃ d : ℝ, 0 < d ∧
      ∀ z : ℝ, |z - b j| < d → |z⁻¹ - (b j)⁻¹| < e := by
    obtain ⟨d, hd, h⟩ := Metric.tendsto_nhds_nhds.mp
      (tendsto_inv₀ (ne_of_gt (hb j))) e he
    refine ⟨d, hd, ?_⟩
    intro z hz
    exact (show dist z⁻¹ (b j)⁻¹ < e from
      h (by simpa only [Real.dist_eq] using hz))
  choose d hd hlocal using hlocal
  have hnon : (range J).Nonempty := ⟨0, mem_range.mpr hJ⟩
  let D := (range J).inf' hnon d
  have hD : 0 < D := (lt_inf'_iff hnon).mpr (fun j _ ↦ hd j)
  refine ⟨J, hJ, D / 2, by positivity, ?_⟩
  filter_upwards [hsep, eventually_ge_atTop J] with n hn hnJ
  obtain ⟨j, hj, hje⟩ := hn
  refine ⟨j, hj, ?_⟩
  by_contra h
  have hclose : |q n j - b j| < d j :=
    (le_of_not_gt h).trans_lt ((half_lt_self hD).trans_le
      (inf'_le d (mem_range.mpr hj)))
  have hsmall := hlocal j (q n j) hclose
  rw [hlink n j (hj.trans_le hnJ)] at hje
  linarith

/-- A finite-head approximation converging to the target cannot remove the
eventual separation. The conclusion retains the same fixed finite head. -/
theorem finite_head_separation_transfer
    (q p : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (J : ℕ) (ε : ℝ)
    (hε : 0 < ε)
    (hsep : ∀ᶠ n in atTop, ∃ j < J, ε < |q n j - b j|)
    (hmodel : ∀ j < J, Tendsto (fun n ↦ p n j) atTop (𝓝 (b j))) :
    ∀ᶠ n in atTop, ∃ j < J, ε / 2 < |q n j - p n j| := by
  have hclose : ∀ᶠ n in atTop, ∀ j ∈ range J, |p n j - b j| < ε / 2 := by
    apply (range J).eventually_all.mpr
    intro j hj
    have h := Metric.tendsto_nhds.mp (hmodel j (mem_range.mp hj))
      (ε / 2) (by positivity)
    simpa only [Real.dist_eq] using h
  filter_upwards [hsep, hclose] with n hn hp
  obtain ⟨j, hj, hjsep⟩ := hn
  refine ⟨j, hj, ?_⟩
  have hjclose := hp j (mem_range.mpr hj)
  have htri := abs_sub_le (q n j) (p n j) (b j)
  linarith

/-- The finite-dimensional version: zero-padding the inverse spectrum
automatically supplies summability, while only the tail needs a uniform bound. -/
theorem finite_head_separation_of_finite_inverse_trace
    (q : ℕ → ℕ → ℝ) (b g : ℕ → ℝ) (A : ℝ)
    (hq : ∀ n j, j < n → 0 < q n j)
    (hb : ∀ j, 0 < b j) (hv : Summable (fun j ↦ (b j)⁻¹)) (hg : Summable g)
    (hgpos : ∀ j, 1 ≤ j → 0 ≤ g j)
    (hbound : ∀ n j, 1 ≤ j → j < n → (q n j)⁻¹ ≤ g j)
    (htrace : Tendsto (fun n ↦ ∑ j ∈ range n, (q n j)⁻¹) atTop (𝓝 A))
    (hne : A ≠ ∑' j, (b j)⁻¹) :
    ∃ J : ℕ, 0 < J ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ n in atTop, J ≤ n ∧ ∃ j < J, ε < |q n j - b j| := by
  let x : ℕ → ℕ → ℝ := fun n j ↦ if j < n then (q n j)⁻¹ else 0
  have hsupp (n j : ℕ) (hj : j ∉ range n) : x n j = 0 := by
    simp only [mem_range] at hj
    simp only [x, if_neg hj]
  have hx (n : ℕ) : Summable (x n) := summable_of_ne_finset_zero (hsupp n)
  have hsum (n : ℕ) : ∑' j, x n j = ∑ j ∈ range n, (q n j)⁻¹ := by
    rw [tsum_eq_sum (hsupp n)]
    apply sum_congr rfl
    intro j hj
    simp only [x, if_pos (mem_range.mp hj)]
  have hxbound (n j : ℕ) (hj : 1 ≤ j) : |x n j| ≤ g j := by
    by_cases hjn : j < n
    · simp only [x, if_pos hjn, abs_of_pos (inv_pos.mpr (hq n j hjn))]
      exact hbound n j hj hjn
    · simpa only [x, if_neg hjn, abs_zero] using hgpos j hj
  have hxtrace : Tendsto (fun n ↦ ∑' j, x n j) atTop (𝓝 A) := by
    simpa only [hsum] using htrace
  obtain ⟨J, hJ, ε, hε, hsep⟩ := finite_head_separation_of_inverse_trace
    x q b g A hx hb hv hg (fun n j hj ↦ if_pos hj) hxbound hxtrace hne
  refine ⟨J, hJ, ε, hε, ?_⟩
  filter_upwards [hsep, eventually_ge_atTop J] with n hn hnJ
  exact ⟨hnJ, hn⟩

/-- Transfer to a remainder on its original scale. For MF-21, take
`s = 2*m`, `h n = 1/(n+2)`, `a` the eigenvalues, and `p` the expansion. -/
theorem finite_head_scaled_remainder_lower_bound
    (a p : ℕ → ℕ → ℝ) (h b : ℕ → ℝ) (s J : ℕ) (ε : ℝ)
    (hh : ∀ n, 0 < h n) (hε : 0 < ε)
    (hsep : ∀ᶠ n in atTop, ∃ j < J, ε < |a n j / (h n)^s - b j|)
    (hmodel : ∀ j < J,
      Tendsto (fun n ↦ p n j / (h n)^s) atTop (𝓝 (b j))) :
    ∀ᶠ n in atTop, ∃ j < J, (ε / 2) * (h n)^s < |a n j - p n j| := by
  have hsep' := finite_head_separation_transfer
    (fun n j ↦ a n j / (h n)^s) (fun n j ↦ p n j / (h n)^s)
    b J ε hε hsep hmodel
  filter_upwards [hsep'] with n hn
  obtain ⟨j, hj, he⟩ := hn
  refine ⟨j, hj, ?_⟩
  have hp : 0 < (h n)^s := pow_pos (hh n) s
  rw [div_sub_div_same, abs_div, abs_of_pos hp] at he
  exact (lt_div_iff₀ hp).mp he

end MF21Audit

#print axioms MF21Audit.finite_head_separation_of_trace
#print axioms MF21Audit.finite_head_separation_of_inverse_trace
#print axioms MF21Audit.finite_head_separation_transfer
#print axioms MF21Audit.finite_head_separation_of_finite_inverse_trace
#print axioms MF21Audit.finite_head_scaled_remainder_lower_bound
