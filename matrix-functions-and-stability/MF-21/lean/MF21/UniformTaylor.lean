import MF21.SmoothQuantization
import Mathlib.Analysis.Normed.Group.Bounded

/-! Uniform parameter-dependent Taylor estimates on compact rectangles. -/
noncomputable section
open Filter Set Finset
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency.types false
namespace MF21Taylor

theorem nat_le_infty (k : ℕ) : (k : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

def verticalDerivative (F : ℝ × ℝ → ℝ) (k : ℕ) (p : ℝ × ℝ) : ℝ :=
  (iteratedFDeriv ℝ k F p) (fun _ ↦ (0, 1))

def coefficient (F : ℝ × ℝ → ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  verticalDerivative F k (s, 0) / (k.factorial : ℝ)

theorem linear_iteratedFDeriv_comp_at {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : G →L[ℝ] E) (F : E → ℝ) (k : ℕ) (x : G)
    (hF : ContDiffAt ℝ k F (L x)) :
    iteratedFDeriv ℝ k (F ∘ L) x =
      (iteratedFDeriv ℝ k F (L x)).compContinuousLinearMap (fun _ ↦ L) := by
  obtain ⟨U, hU, hx, hFU⟩ := hF.contDiffOn' le_rfl (by simp)
  simp only [Set.insert_eq_of_mem (Set.mem_univ _), Set.univ_inter] at hFU
  have hpre : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have hcomp : ContDiffAt ℝ k (F ∘ L) x := hF.comp x L.contDiff.contDiffAt
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv hpre.uniqueDiffOn hcomp hx,
    ← iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn hF hx]
  exact L.iteratedFDerivWithin_comp_right hFU hU.uniqueDiffOn hpre.uniqueDiffOn hx le_rfl

theorem slice_iteratedDeriv_at (F : ℝ × ℝ → ℝ) (k : ℕ) (s t : ℝ)
    (hF : ContDiffAt ℝ k F (s, t)) :
    iteratedDeriv k (fun h ↦ F (s, h)) t = verticalDerivative F k (s, t) := by
  let L := ContinuousLinearMap.inr ℝ ℝ ℝ
  let G : ℝ × ℝ → ℝ := fun p ↦ F ((s, 0) + p)
  have hG : ContDiffAt ℝ k G (0, t) := by
    have ho : ContDiffAt ℝ k F ((s, (0 : ℝ)) + (0, t)) := by
      simpa only [Prod.mk_add_mk, add_zero, zero_add] using hF
    exact ho.comp _ (contDiffAt_const.add contDiffAt_id)
  have H := linear_iteratedFDeriv_comp_at L G k t hG
  have H' := congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ ℝ) ℝ ↦
    T (fun _ ↦ 1)) H
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at H'
  have hcomp : G ∘ L = fun h ↦ F (s, h) := by
    funext h
    simp [G, L]
  rw [hcomp] at H'
  simp only [L, ContinuousLinearMap.inr_apply] at H'
  rw [show G = (fun p ↦ F ((s, 0) + p)) from rfl, iteratedFDeriv_comp_add_left] at H'
  simpa only [Prod.mk_add_mk, add_zero, zero_add, verticalDerivative, iteratedDeriv] using H'

theorem slice_iteratedDeriv (F : ℝ × ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    (k : ℕ) (s t : ℝ) :
    iteratedDeriv k (fun h ↦ F (s, h)) t = verticalDerivative F k (s, t) := by
  let L := ContinuousLinearMap.inr ℝ ℝ ℝ
  let G : ℝ × ℝ → ℝ := fun p ↦ F ((s, 0) + p)
  have hG : ContDiff ℝ ∞ G := hF.comp (contDiff_const.add contDiff_id)
  have H := L.iteratedFDeriv_comp_right hG t (i := k) (nat_le_infty k)
  have H' := congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ ℝ) ℝ ↦
    T (fun _ ↦ 1)) H
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at H'
  have hcomp : G ∘ L = fun h ↦ F (s, h) := by
    funext h
    simp [G, L]
  rw [hcomp] at H'
  simp only [L, ContinuousLinearMap.inr_apply] at H'
  rw [show G = (fun p ↦ F ((s, 0) + p)) from rfl, iteratedFDeriv_comp_add_left] at H'
  simpa only [Prod.mk_add_mk, add_zero, zero_add, verticalDerivative, iteratedDeriv] using H'

theorem verticalDerivative_continuous (F : ℝ × ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (k : ℕ) :
    Continuous (verticalDerivative F k) := by
  have hc : Continuous (iteratedFDeriv ℝ k F) :=
    (hF.iteratedFDeriv_right (m := 0) (by simpa only [zero_add] using nat_le_infty k)).continuous
  exact (continuous_eval_const (fun _ : Fin k ↦ ((0 : ℝ), (1 : ℝ)))).comp hc

theorem coefficient_continuous (F : ℝ × ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (k : ℕ) :
    Continuous (coefficient F k) :=
  ((verticalDerivative_continuous F hF k).comp (continuous_id.prodMk continuous_const)).div_const _

theorem coefficient_zero (F : ℝ × ℝ → ℝ) (s : ℝ) : coefficient F 0 s = F (s, 0) := by
  simp [coefficient, verticalDerivative]

theorem verticalDerivative_continuousAt (F : ℝ × ℝ → ℝ) (k : ℕ) (p : ℝ × ℝ)
    (hF : ContDiffAt ℝ ∞ F p) : ContinuousAt (verticalDerivative F k) p := by
  have hc : ContinuousAt (iteratedFDeriv ℝ k F) p :=
    (hF.iteratedFDeriv_right (m := 0) (by simpa only [zero_add] using nat_le_infty k)).continuousAt
  exact (continuous_eval_const (fun _ : Fin k ↦ ((0 : ℝ), (1 : ℝ)))).continuousAt.comp hc

theorem coefficient_continuousOn (F : ℝ × ℝ → ℝ) (a b : ℝ)
    (hF : ∀ s ∈ Icc a b, ContDiffAt ℝ ∞ F (s, 0)) (k : ℕ) :
    ContinuousOn (coefficient F k) (Icc a b) := by
  intro s hs
  apply ContinuousAt.continuousWithinAt
  change ContinuousAt (fun u : ℝ ↦ verticalDerivative F k (u, 0) / (k.factorial : ℝ)) s
  exact ((verticalDerivative_continuousAt F k (s, 0) (hF s hs)).comp (f := fun u : ℝ ↦ (u, (0 : ℝ)))
    (show ContinuousAt (fun u : ℝ ↦ (u, (0 : ℝ))) s from
      continuousAt_id.prodMk continuousAt_const)).div_const _

/-- The Taylor coefficients are one common continuous family, with a uniform
remainder bound at every finite order on any compact parameter interval. -/
theorem uniform_taylor_bound_on (F : ℝ × ℝ → ℝ)
    (a b H : ℝ) (hH : 0 < H)
    (hF : ∀ z ∈ Icc a b ×ˢ Icc 0 H, ContDiffAt ℝ ∞ F z) (p : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ s ∈ Icc a b, ∀ h ∈ Icc 0 H,
      |F (s, h) - ∑ k ∈ range (p + 1), coefficient F k s * h ^ k| ≤ D * h ^ (p + 1) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (show ContinuousOn (verticalDerivative F (p + 1)) (Icc a b ×ˢ Icc 0 H) from
      fun z hz ↦ (verticalDerivative_continuousAt F (p + 1) z (hF z hz)).continuousWithinAt)
    (s := Icc a b ×ˢ Icc 0 H)
  refine ⟨(|C| + 1) / (p.factorial : ℝ), by positivity, ?_⟩
  intro s hs h hh
  have hslice (t : ℝ) (ht : t ∈ Icc 0 H) : ContDiffAt ℝ ∞ (fun t ↦ F (s, t)) t :=
    (hF (s, t) ⟨hs, ht⟩).comp t (contDiffAt_const.prodMk contDiffAt_id)
  have he (k : ℕ) (y : ℝ) (hy : y ∈ Icc 0 H) :
      iteratedDerivWithin k (fun t ↦ F (s, t)) (Icc 0 H) y =
        verticalDerivative F k (s, y) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hH)
      ((hslice y hy).of_le (nat_le_infty k)) hy]
    exact slice_iteratedDeriv_at F k s y ((hF (s, y) ⟨hs, hy⟩).of_le (nat_le_infty k))
  have hbound : ∀ y ∈ Icc 0 H,
      ‖iteratedDerivWithin (p + 1) (fun t ↦ F (s, t)) (Icc 0 H) y‖ ≤ |C| + 1 := by
    intro y hy
    rw [he (p + 1) y hy]
    exact (hC (s, y) ⟨hs, hy⟩).trans (by linarith [le_abs_self C])
  have ht := taylor_mean_remainder_bound hH.le
    (show ContDiffOn ℝ (p + 1) (fun t ↦ F (s, t)) (Icc 0 H) from
      fun t ht ↦ ((hslice t ht).of_le (nat_le_infty (p + 1))).contDiffWithinAt) hh hbound
  have hpoly : taylorWithinEval (fun t ↦ F (s, t)) p (Icc 0 H) 0 h =
      ∑ k ∈ range (p + 1), coefficient F k s * h ^ k := by
    rw [taylor_within_apply]
    apply sum_congr rfl
    intro k hk
    rw [he k 0 ⟨le_rfl, hH.le⟩]
    simp only [sub_zero, smul_eq_mul, coefficient]
    ring
  rw [hpoly, Real.norm_eq_abs, sub_zero] at ht
  exact ht.trans_eq (by ring)


/-- Dividing a uniform order-(q+1) Taylor remainder by h^q leaves a vanishing
error. This applies to any parameter sequence in the compact interval. -/
theorem normalized_remainder_tendsto (F : ℝ × ℝ → ℝ)
    (a b H : ℝ) (hH : 0 < H)
    (hF : ∀ z ∈ Icc a b ×ˢ Icc 0 H, ContDiffAt ℝ ∞ F z) (q : ℕ)
    (s h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (hmem : ∀ᶠ n in atTop, s n ∈ Icc a b ∧ h n ∈ Ioc 0 H) :
    Tendsto (fun n ↦ (F (s n, h n) -
      ∑ k ∈ range (q + 1), coefficient F k (s n) * h n ^ k) / h n ^ q)
      atTop (𝓝 0) := by
  obtain ⟨D, hD, hb⟩ := uniform_taylor_bound_on F a b H hH hF q
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero' (Eventually.of_forall fun n ↦ abs_nonneg _) ?_
    (by simpa only [mul_zero] using hh.const_mul D)
  filter_upwards [hmem] with n hn
  rw [abs_div, abs_of_pos (pow_pos hn.2.1 q)]
  apply (div_le_iff₀ (pow_pos hn.2.1 q)).mpr
  have he := hb (s n) hn.1 (h n) ⟨hn.2.1.le, hn.2.2⟩
  calc
    _ ≤ D * h n ^ (q + 1) := he
    _ = D * h n * h n ^ q := by ring

/-- A model's scaled fixed-index limit passes to its common Taylor coefficients. -/
theorem taylor_profile_tendsto (F : ℝ × ℝ → ℝ)
    (a b H : ℝ) (hH : 0 < H)
    (hF : ∀ z ∈ Icc a b ×ˢ Icc 0 H, ContDiffAt ℝ ∞ F z) (q : ℕ)
    (s h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (hmem : ∀ᶠ n in atTop, s n ∈ Icc a b ∧ h n ∈ Ioc 0 H)
    (L : ℝ) (hL : Tendsto (fun n ↦ F (s n, h n) / h n ^ q) atTop (𝓝 L)) :
    Tendsto (fun n ↦ (∑ k ∈ range (q + 1), coefficient F k (s n) * h n ^ k) /
      h n ^ q) atTop (𝓝 L) := by
  have hr := normalized_remainder_tendsto F a b H hH hF q s h hh hmem
  have ht := hL.sub hr
  simpa only [sub_div, sub_sub_cancel, sub_zero] using ht


/-- Evaluation of the derivative tensor at a fixed direction is linear and
continuous, so the common coefficients inherit all smoothness orders. -/
def evaluateDirection (k : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ ℝ × ℝ) ℝ →L[ℝ] ℝ where
  toFun T := T (fun _ ↦ (0, 1))
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  cont := continuous_eval_const _

theorem coefficient_contDiffAt (F : ℝ × ℝ → ℝ) (k : ℕ) (s : ℝ)
    (hF : ContDiffAt ℝ ∞ F (s, 0)) : ContDiffAt ℝ ∞ (coefficient F k) s := by
  have hd : ContDiffAt ℝ ∞ (iteratedFDeriv ℝ k F) (s, 0) :=
    hF.iteratedFDeriv_right (m := ∞) (by
      change ((⊤ : ℕ∞) : WithTop ℕ∞) + ((k : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      rw [← WithTop.coe_add]
      exact WithTop.coe_le_coe.mpr le_top)
  have hv : ContDiffAt ℝ ∞ (verticalDerivative F k) (s, 0) :=
    (evaluateDirection k).contDiff.contDiffAt.comp (s, 0) hd
  exact (hv.comp (f := fun u : ℝ ↦ (u, (0 : ℝ))) s
    (contDiffAt_id.prodMk contDiffAt_const)).div_const _

end MF21Taylor
#print axioms MF21Taylor.slice_iteratedDeriv
#print axioms MF21Taylor.coefficient_continuous

#print axioms MF21Taylor.uniform_taylor_bound_on

#print axioms MF21Taylor.coefficient_continuousOn
#print axioms MF21Taylor.taylor_profile_tendsto

#print axioms MF21Taylor.coefficient_contDiffAt
