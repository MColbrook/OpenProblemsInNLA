import MF21Restart.KernelRiemannApprox

/-! The concrete right sum with h=1/n, zero-step limiting integrand, and
a lower endpoint displaced by at most one cell. Prior statement lock:
KERNEL_SHIFTED_SUM_STATEMENTS.md. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

theorem finiteKernelIntegrand_continuousOn_interval
    (m : ℕ) (h x y : ℝ) (hh : h ∈ Set.Icc 0 1)
    (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    ContinuousOn (finiteKernelIntegrand m h x y) (Set.Icc (1 / 4 : ℝ) 1) := by
  let p : ℝ → Fin 4 → ℝ := fun t => ![h, x, y, t]
  have hp : Continuous p := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const
    · exact continuous_id
  have hc := (finiteKernelIntegrand_continuousOn_box m).comp hp.continuousOn
    (fun t ht => kernelParameters_mem_box h x y t hh hx hy ht)
  change ContinuousOn (finiteKernelIntegrand m h x y) (Set.Icc (1 / 4 : ℝ) 1) at hc
  exact hc

theorem finiteKernelIntegrand_uniform_shifted_sum (m : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 4 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ x y : ℝ,
        x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 →
        ∀ a : ℕ, a ≤ n → (1 / 4 : ℝ) ≤ (a : ℝ) / n →
        ∀ b : ℝ, b ∈ Set.Icc ((a : ℝ) / n) 1 → b - (a : ℝ) / n ≤ 1 / n →
          |(1 / (n : ℝ)) *
              (∑ k ∈ Finset.Ico a n,
                finiteKernelIntegrand m (1 / n) x y (((k + 1 : ℕ) : ℝ) / n)) -
            ∫ t in b..1, finiteKernelIntegrand m 0 x y t| ≤ ε := by
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨N₁, hN₁, hsum⟩ := finiteKernelIntegrand_uniform_right_sum m (ε / 3) hthird
  obtain ⟨δ, hδ, hclose⟩ := finiteKernelIntegrand_uniform_zero_step m (ε / 3) hthird
  obtain ⟨C, hC, hbound⟩ := finiteKernelIntegrand_uniform_bound m
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (max (1 / δ) (3 * C / ε))
  refine ⟨max 4 (max N₁ N₂), le_max_left _ _, ?_⟩
  intro n hn x y hx hy a han hstart b hb hshift
  have hn4 : 4 ≤ n := (le_max_left _ _).trans hn
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn₂ : N₂ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hN₂n : (N₂ : ℝ) ≤ n := by exact_mod_cast hn₂
  have hh : (1 / (n : ℝ)) ∈ Set.Icc 0 1 := by
    constructor
    · positivity
    · exact (div_le_one hnpos).mpr hnreal
  have hsmall : 1 / (n : ℝ) < δ := by
    have ht : 1 / δ < (n : ℝ) := ((le_max_left _ _).trans_lt hN₂).trans_le hN₂n
    have hm := (div_lt_iff₀ hδ).mp ht
    apply (div_lt_iff₀ hnpos).mpr
    simpa only [mul_comm] using hm
  have hCsmall : C * (1 / (n : ℝ)) ≤ ε / 3 := by
    have ht : 3 * C / ε < (n : ℝ) := ((le_max_right _ _).trans_lt hN₂).trans_le hN₂n
    have hm := (div_lt_iff₀ hε).mp ht
    have hd : C / (n : ℝ) < ε / 3 := (div_lt_iff₀ hnpos).mpr (by nlinarith)
    simpa only [div_eq_mul_inv, one_mul] using hd.le
  let q : ℝ := (a : ℝ) / n
  have hq0 : 0 ≤ q := div_nonneg (Nat.cast_nonneg a) hnpos.le
  have hq1 : q ≤ 1 := (div_le_one hnpos).mpr (by exact_mod_cast han)
  have hsub : Set.Icc q 1 ⊆ Set.Icc (1 / 4 : ℝ) 1 := by
    intro t ht
    exact ⟨hstart.trans ht.1, ht.2⟩
  have hf := finiteKernelIntegrand_continuousOn_interval m (1 / n) x y hh hx hy
  have hf₀ := finiteKernelIntegrand_continuousOn_interval m 0 x y
    ⟨le_rfl, zero_le_one⟩ hx hy
  have hi : IntervalIntegrable (finiteKernelIntegrand m (1 / n) x y)
      MeasureTheory.volume q 1 := (hf.mono hsub).intervalIntegrable_of_Icc hq1
  have hi₀ : IntervalIntegrable (finiteKernelIntegrand m 0 x y)
      MeasureTheory.volume q 1 := (hf₀.mono hsub).intervalIntegrable_of_Icc hq1
  have hchange : |(∫ t in q..1, finiteKernelIntegrand m (1 / n) x y t) -
      ∫ t in q..1, finiteKernelIntegrand m 0 x y t| ≤ ε / 3 := by
    have he := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := q) (b := 1) (C := ε / 3)
      (f := fun t => finiteKernelIntegrand m (1 / n) x y t -
        finiteKernelIntegrand m 0 x y t) (by
        intro t ht
        have ht' : t ∈ Set.Ioc q 1 := by simpa only [Set.uIoc_of_le hq1] using ht
        rw [Real.norm_eq_abs]
        exact (hclose (1 / n) x y t hh hx hy (hsub ⟨ht'.1.le, ht'.2⟩) hsmall).le)
    rw [intervalIntegral.integral_sub hi hi₀, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hq1)] at he
    exact he.trans (by nlinarith only [hthird.le, hq0])
  have hqb : q ≤ b := hb.1
  have hb1 : b ≤ 1 := hb.2
  have hiqb : IntervalIntegrable (finiteKernelIntegrand m 0 x y)
      MeasureTheory.volume q b :=
    (hf₀.mono (fun t ht => ⟨hstart.trans ht.1, ht.2.trans hb1⟩)).intervalIntegrable_of_Icc hqb
  have hib1 : IntervalIntegrable (finiteKernelIntegrand m 0 x y)
      MeasureTheory.volume b 1 :=
    (hf₀.mono (fun t ht => ⟨(hstart.trans hqb).trans ht.1, ht.2⟩)).intervalIntegrable_of_Icc hb1
  have hmove : |(∫ t in q..1, finiteKernelIntegrand m 0 x y t) -
      ∫ t in b..1, finiteKernelIntegrand m 0 x y t| ≤ ε / 3 := by
    have he := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := q) (b := b) (C := C) (f := finiteKernelIntegrand m 0 x y) (by
        intro t ht
        have ht' : t ∈ Set.Ioc q b := by simpa only [Set.uIoc_of_le hqb] using ht
        have hp := hbound ![0, x, y, t]
          (kernelParameters_mem_box 0 x y t ⟨le_rfl, zero_le_one⟩ hx hy
            ⟨hstart.trans ht'.1.le, ht'.2.trans hb1⟩)
        change |finiteKernelIntegrand m 0 x y t| ≤ C at hp
        simpa only [Real.norm_eq_abs] using hp)
    have hadd := intervalIntegral.integral_add_adjacent_intervals hiqb hib1
    have hid : (∫ t in q..1, finiteKernelIntegrand m 0 x y t) -
        ∫ t in b..1, finiteKernelIntegrand m 0 x y t =
        ∫ t in q..b, finiteKernelIntegrand m 0 x y t := by linarith only [hadd]
    rw [hid]
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hqb)] at he
    exact he.trans ((mul_le_mul_of_nonneg_left hshift hC.le).trans hCsmall)
  have hs := hsum n hn₁ (1 / n) x y hh hx hy a han hstart
  let S : ℝ := (1 / (n : ℝ)) * ∑ k ∈ Finset.Ico a n,
    finiteKernelIntegrand m (1 / n) x y (((k + 1 : ℕ) : ℝ) / n)
  have hab := abs_sub_le S (∫ t in q..1, finiteKernelIntegrand m (1 / n) x y t)
    (∫ t in b..1, finiteKernelIntegrand m 0 x y t)
  have hbc := abs_sub_le (∫ t in q..1, finiteKernelIntegrand m (1 / n) x y t)
    (∫ t in q..1, finiteKernelIntegrand m 0 x y t)
    (∫ t in b..1, finiteKernelIntegrand m 0 x y t)
  change |S - ∫ t in b..1, finiteKernelIntegrand m 0 x y t| ≤ ε
  change |S - ∫ t in q..1, finiteKernelIntegrand m (1 / n) x y t| ≤ ε / 3 at hs
  linarith only [hs, hchange, hmove, hab, hbc]

#print axioms finiteKernelIntegrand_continuousOn_interval
#print axioms finiteKernelIntegrand_uniform_shifted_sum

end MF21Restart
