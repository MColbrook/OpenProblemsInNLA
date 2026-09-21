import MF21Restart.ScaledRising
import MF21Restart.RiemannCellBound
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-! Uniform continuity and right-endpoint sums for the concrete inverse
integrand. See KERNEL_RIEMANN_APPROX_STATEMENTS.md for the prior lock. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

theorem kernelParameters_mem_box (h x y t : ℝ)
    (hh : h ∈ Set.Icc 0 1) (hx : x ∈ Set.Icc 0 1)
    (hy : y ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc (1 / 4) 1) :
    ![h, x, y, t] ∈ kernelParameterBox := by
  constructor
  · intro i
    fin_cases i
    · change 0 ≤ h; exact hh.1
    · change 0 ≤ x; exact hx.1
    · change 0 ≤ y; exact hy.1
    · change 1 / 4 ≤ t; exact ht.1
  · intro i
    fin_cases i
    · change h ≤ 1; exact hh.2
    · change x ≤ 1; exact hx.2
    · change y ≤ 1; exact hy.2
    · change t ≤ 1; exact ht.2

theorem finiteKernelIntegrand_uniform_zero_step (m : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ h x y t : ℝ, h ∈ Set.Icc 0 1 → x ∈ Set.Icc 0 1 →
        y ∈ Set.Icc 0 1 → t ∈ Set.Icc (1 / 4) 1 → h < δ →
          |finiteKernelIntegrand m h x y t - finiteKernelIntegrand m 0 x y t| < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (finiteKernelIntegrand_uniformContinuousOn_box m) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro h x y t hh hx hy ht hsmall
  have hd : dist (![h, x, y, t] : Fin 4 → ℝ) ![0, x, y, t] < δ := by
    apply (dist_pi_lt_iff hδ).mpr
    intro i
    fin_cases i
    · change dist h 0 < δ
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hh.1] using hsmall
    · change dist x x < δ; simpa only [dist_self] using hδ
    · change dist y y < δ; simpa only [dist_self] using hδ
    · change dist t t < δ; simpa only [dist_self] using hδ
  have hb := hclose ![h, x, y, t] (kernelParameters_mem_box h x y t hh hx hy ht)
    ![0, x, y, t] (kernelParameters_mem_box 0 x y t ⟨le_rfl, zero_le_one⟩ hx hy ht) hd
  change dist (finiteKernelIntegrand m h x y t) (finiteKernelIntegrand m 0 x y t) < ε at hb
  simpa only [Real.dist_eq] using hb

theorem finiteKernelIntegrand_uniform_right_sum (m : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ h x y : ℝ,
        h ∈ Set.Icc 0 1 → x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 →
        ∀ a : ℕ, a ≤ n → (1 / 4 : ℝ) ≤ (a : ℝ) / n →
          |(1 / (n : ℝ)) *
              (∑ k ∈ Finset.Ico a n,
                finiteKernelIntegrand m h x y (((k + 1 : ℕ) : ℝ) / n)) -
            ∫ t in (a : ℝ) / n..1, finiteKernelIntegrand m h x y t| ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (finiteKernelIntegrand_uniformContinuousOn_box m) ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (1 / δ))
  have hN1 : 1 ≤ N := by
    have hNr : (1 : ℝ) < N := (le_max_left _ _).trans_lt hN
    exact_mod_cast hNr.le
  refine ⟨N, hN1, ?_⟩
  intro n hn h x y hh hx hy a han hstart
  have hn1 : 1 ≤ n := hN1.trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hsmall : 1 / (n : ℝ) < δ := by
    have hthreshold : 1 / δ < (n : ℝ) :=
      ((le_max_right _ _).trans_lt hN).trans_le hNn
    have hmul := (div_lt_iff₀ hδ).mp hthreshold
    apply (div_lt_iff₀ hnpos).mpr
    simpa only [mul_comm] using hmul
  let q : ℕ → ℝ := fun k => (k : ℝ) / n
  have hqmono : Monotone q := by
    intro k ell hkl
    exact div_le_div_of_nonneg_right (by exact_mod_cast hkl) hnpos.le
  have hqn : q n = 1 := div_self hnpos.ne'
  have hqstep (k : ℕ) : q (k + 1) - q k = 1 / (n : ℝ) := by
    dsimp only [q]
    push_cast
    ring
  have hcellSubset (k : ℕ) (hk : k ∈ Finset.Ico a n) :
      Set.Icc (q k) (q (k + 1)) ⊆ Set.Icc (1 / 4 : ℝ) 1 := by
    intro t ht
    have hk' := Finset.mem_Ico.mp hk
    constructor
    · exact hstart.trans ((hqmono hk'.1).trans ht.1)
    · exact ht.2.trans (by simpa only [hqn] using hqmono (by omega : k + 1 ≤ n))
  let p : ℝ → Fin 4 → ℝ := fun t => ![h, x, y, t]
  have hp : Continuous p := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const
    · exact continuous_id
  have hfc : ContinuousOn (finiteKernelIntegrand m h x y) (Set.Icc (1 / 4 : ℝ) 1) := by
    have hc := (finiteKernelIntegrand_continuousOn_box m).comp hp.continuousOn
      (fun t ht => kernelParameters_mem_box h x y t hh hx hy ht)
    change ContinuousOn (finiteKernelIntegrand m h x y) (Set.Icc (1 / 4 : ℝ) 1) at hc
    exact hc
  have hf (k : ℕ) (hk : k ∈ Finset.Ico a n) :
      IntervalIntegrable (finiteKernelIntegrand m h x y) MeasureTheory.volume
        (q k) (q (k + 1)) :=
    (hfc.mono (hcellSubset k hk)).intervalIntegrable_of_Icc (hqmono (Nat.le_succ k))
  have hosc (k : ℕ) (hk : k ∈ Finset.Ico a n)
      (t : ℝ) (ht : t ∈ Set.Icc (q k) (q (k + 1))) :
      |finiteKernelIntegrand m h x y (q (k + 1)) - finiteKernelIntegrand m h x y t| ≤ ε := by
    have htbox := hcellSubset k hk ht
    have hrightbox := hcellSubset k hk
      (show q (k + 1) ∈ Set.Icc (q k) (q (k + 1)) from
        ⟨hqmono (Nat.le_succ k), le_rfl⟩)
    have htdist : dist (q (k + 1)) t < δ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.2)]
      have hstep := hqstep k
      linarith [ht.1]
    have hpdist : dist (p (q (k + 1))) (p t) < δ := by
      apply (dist_pi_lt_iff hδ).mpr
      intro i
      fin_cases i
      · change dist h h < δ; simpa only [dist_self] using hδ
      · change dist x x < δ; simpa only [dist_self] using hδ
      · change dist y y < δ; simpa only [dist_self] using hδ
      · exact htdist
    have hb := hclose (p (q (k + 1)))
      (kernelParameters_mem_box h x y (q (k + 1)) hh hx hy hrightbox)
      (p t) (kernelParameters_mem_box h x y t hh hx hy htbox) hpdist
    change dist (finiteKernelIntegrand m h x y (q (k + 1)))
      (finiteKernelIntegrand m h x y t) < ε at hb
    exact (show |finiteKernelIntegrand m h x y (q (k + 1)) -
      finiteKernelIntegrand m h x y t| < ε by simpa only [Real.dist_eq] using hb).le
  have hb := riemann_right_sum_error_bound q hqmono a n han
    (finiteKernelIntegrand m h x y) ε hf hosc
  have hsum : (∑ k ∈ Finset.Ico a n,
      (q (k + 1) - q k) * finiteKernelIntegrand m h x y (q (k + 1))) =
        (1 / (n : ℝ)) * ∑ k ∈ Finset.Ico a n,
          finiteKernelIntegrand m h x y (((k + 1 : ℕ) : ℝ) / n) := by
    simp_rw [hqstep]
    rw [Finset.mul_sum]
  rw [hsum, hqn] at hb
  exact hb.trans (by
    have hqa : 0 ≤ q a := div_nonneg (Nat.cast_nonneg a) hnpos.le
    nlinarith only [hqa, hε.le])

#print axioms kernelParameters_mem_box
#print axioms finiteKernelIntegrand_uniform_zero_step
#print axioms finiteKernelIntegrand_uniform_right_sum

end MF21Restart
