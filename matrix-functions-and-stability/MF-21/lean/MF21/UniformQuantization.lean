import MF21.UniformTaylor
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! A single smooth implicit inverse on a compact strip. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency.types false
namespace MF21Quantization

/-- Implicit inversion at any regular solution of the quantization equation. -/
theorem exists_local_smooth_inverse_at (eta : ℝ → ℝ) (p : ℝ × ℝ) (theta : ℝ)
    (heta : ContDiffAt ℝ ∞ eta theta)
    (heq : theta = p.1 + p.2 * eta theta)
    (hreg : 1 - p.2 * deriv eta theta ≠ 0) :
    ∃ Y : ℝ × ℝ → ℝ, Y p = theta ∧ ContDiffAt ℝ ∞ Y p ∧
      ∀ᶠ q in 𝓝 p, Y q = q.1 + q.2 * eta (Y q) := by
  have hc : ContDiffAt ℝ ∞ (equation eta) (p, theta) := by
    unfold equation
    exact (contDiffAt_snd.sub contDiffAt_fst.fst).sub
      (contDiffAt_fst.snd.mul (heta.comp _ contDiffAt_snd))
  have hy : HasFDerivAt (fun q : (ℝ × ℝ) × ℝ ↦ q.2)
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ) (p, theta) := hasFDerivAt_snd
  have hp : HasFDerivAt (fun q : (ℝ × ℝ) × ℝ ↦ q.1)
      (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ) (p, theta) := hasFDerivAt_fst
  have he := (heta.differentiableAt (by simp)).hasDerivAt.hasFDerivAt.comp (p, theta) hy
  have hd := (hy.sub hp.fst).sub (hp.snd.mul he)
  change HasFDerivAt (equation eta) _ (p, theta) at hd
  have hpartial : (fderiv ℝ (equation eta) (p, theta)).comp
      (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ) =
      (1 - p.2 * deriv eta theta) • ContinuousLinearMap.id ℝ ℝ := by
    rw [hd.fderiv]
    ext
    simp
  have hi : ((fderiv ℝ (equation eta) (p, theta)).comp
      (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ)).IsInvertible := by
    rw [hpartial]
    refine ⟨ContinuousLinearEquiv.smulLeft (Units.mk0 (1 - p.2 * deriv eta theta) hreg), ?_⟩
    ext
    simp
  let Y := hc.implicitFunction (by simp) hi
  refine ⟨Y, hc.implicitFunction_apply_self (by simp) hi,
    hc.contDiffAt_implicitFunction (by simp) hi, ?_⟩
  filter_upwards [hc.eventually_apply_implicitFunction (by simp) hi] with q hq
  change equation eta (q, Y q) = equation eta (p, theta) at hq
  simp only [equation] at hq
  linarith

def intervalInverse (eta : ℝ → ℝ) (lo hi : ℝ) (p : ℝ × ℝ) : ℝ :=
  Function.invFunOn (fun theta ↦ theta - p.2 * eta theta) (Icc lo hi) p.1

/-- The interval inverse agrees locally with the smooth implicit branch whenever
nearby one-dimensional equations are injective on the interval. -/
theorem intervalInverse_contDiffAt (eta : ℝ → ℝ) (lo hi : ℝ) (p : ℝ × ℝ)
    (hmem : intervalInverse eta lo hi p ∈ Ioo lo hi)
    (heta : ContDiffAt ℝ ∞ eta (intervalInverse eta lo hi p))
    (heq : intervalInverse eta lo hi p = p.1 + p.2 * eta (intervalInverse eta lo hi p))
    (hreg : 1 - p.2 * deriv eta (intervalInverse eta lo hi p) ≠ 0)
    (hinj : ∀ᶠ q in 𝓝 p, InjOn (fun theta ↦ theta - q.2 * eta theta) (Icc lo hi)) :
    ContDiffAt ℝ ∞ (intervalInverse eta lo hi) p := by
  obtain ⟨Y, hYp, hY, he⟩ := exists_local_smooth_inverse_at eta p _ heta heq hreg
  have hm : ∀ᶠ q in 𝓝 p, Y q ∈ Ioo lo hi :=
    hY.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds (hYp.symm ▸ hmem))
  apply hY.congr_of_eventuallyEq
  filter_upwards [he, hm, hinj] with q hq hmq hiq
  have heq' : Y q - q.2 * eta (Y q) = q.1 := by linarith
  unfold intervalInverse
  rw [← heq']
  exact hiq.leftInvOn_invFunOn ⟨hmq.1.le, hmq.2.le⟩


/-- Quantitative elementary conditions giving one inverse and its smoothness on
an entire compact strip. The derivative condition is imposed on a larger strip
so that smoothness at the strip boundary is ambient smoothness. -/
theorem intervalInverse_strip (eta : ℝ → ℝ) (lo hi a b H M K : ℝ)
    (hab : a ≤ b) (hlo : lo < a) (hhi : b < hi) (hH : 0 < H)
    (hM : 0 ≤ M) (hK : 0 ≤ K)
    (heta : ∀ theta ∈ Icc lo hi, ContDiffAt ℝ ∞ eta theta)
    (hbound : ∀ theta ∈ Icc lo hi, |eta theta| ≤ M)
    (hderiv : ∀ theta ∈ Icc lo hi, |deriv eta theta| ≤ K)
    (hleft : H * M < a - lo) (hright : H * M < hi - b)
    (hsmall : 2 * H * K < 1) :
    ∀ p ∈ Icc a b ×ˢ Icc 0 H,
      intervalInverse eta lo hi p ∈ Ioo lo hi ∧
      intervalInverse eta lo hi p = p.1 + p.2 * eta (intervalInverse eta lo hi p) ∧
      ContDiffAt ℝ ∞ (intervalInverse eta lo hi) p := by
  have hlohi : lo ≤ hi := by linarith
  have hpos (h : ℝ) (hh : |h| < 2 * H) (theta : ℝ) (ht : theta ∈ Icc lo hi) :
      0 < 1 - h * deriv eta theta := by
    have hb : h * deriv eta theta ≤ 2 * H * K := calc
      _ ≤ |h * deriv eta theta| := le_abs_self _
      _ = |h| * |deriv eta theta| := abs_mul _ _
      _ ≤ (2 * H) * K := mul_le_mul hh.le (hderiv theta ht) (abs_nonneg _) (by positivity)
    linarith
  have hmono (h : ℝ) (hh : |h| < 2 * H) :
      StrictMonoOn (fun theta ↦ theta - h * eta theta) (Icc lo hi) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro theta ht
      exact (continuousAt_id.sub ((heta theta ht).continuousAt.const_mul h)).continuousWithinAt
    · intro theta ht
      have ht' := interior_subset ht
      have hd := (hasDerivAt_id theta).sub
        (((heta theta ht').differentiableAt (by simp)).hasDerivAt.const_mul h)
      change 0 < deriv (id - fun y ↦ h * eta y) theta
      rw [hd.deriv]
      exact hpos h hh theta ht'
  intro p hp
  have habsp : |p.2| ≤ H := by rw [abs_of_nonneg hp.2.1]; exact hp.2.2
  have hnear : |p.2| < 2 * H := lt_of_le_of_lt habsp (by linarith)
  have hpbound (theta : ℝ) (ht : theta ∈ Icc lo hi) : |p.2 * eta theta| ≤ H * M := by
    rw [abs_mul]
    exact mul_le_mul habsp (hbound theta ht) (abs_nonneg _) hH.le
  have hleft' : lo - p.2 * eta lo < p.1 := by
    have hb := hpbound lo ⟨le_rfl, hlohi⟩
    have hl := neg_abs_le (p.2 * eta lo)
    linarith [hp.1.1]
  have hright' : p.1 < hi - p.2 * eta hi := by
    have hb := hpbound hi ⟨hlohi, le_rfl⟩
    have hr := le_abs_self (p.2 * eta hi)
    linarith [hp.1.2]
  have hex : ∃ theta ∈ Icc lo hi, theta - p.2 * eta theta = p.1 :=
    intermediate_value_Icc hlohi
      (fun theta ht ↦ (continuousAt_id.sub
        ((heta theta ht).continuousAt.const_mul p.2)).continuousWithinAt)
      ⟨hleft'.le, hright'.le⟩
  have hm : intervalInverse eta lo hi p ∈ Icc lo hi := Function.invFunOn_mem hex
  have he : intervalInverse eta lo hi p - p.2 * eta (intervalInverse eta lo hi p) = p.1 :=
    Function.invFunOn_eq hex
  have hmo : intervalInverse eta lo hi p ∈ Ioo lo hi := by
    constructor
    · by_contra h
      have hh : intervalInverse eta lo hi p = lo := le_antisymm (not_lt.mp h) hm.1
      rw [hh] at he
      linarith
    · by_contra h
      have hh : intervalInverse eta lo hi p = hi := le_antisymm hm.2 (not_lt.mp h)
      rw [hh] at he
      linarith
  have heq : intervalInverse eta lo hi p = p.1 + p.2 * eta (intervalInverse eta lo hi p) := by
    linarith
  refine ⟨hmo, heq, intervalInverse_contDiffAt eta lo hi p hmo (heta _ hm) heq
    (ne_of_gt (hpos p.2 hnear _ hm)) ?_⟩
  have hn : ∀ᶠ q : ℝ × ℝ in 𝓝 p, q.2 ∈ Ioo (-2 * H) (2 * H) :=
    continuousAt_snd.eventually_mem (isOpen_Ioo.mem_nhds (by
      simpa only [neg_mul, mem_Ioo] using abs_lt.mp hnear))
  filter_upwards [hn] with q hq
  exact (hmono q.2 (abs_lt.mpr (by simpa only [neg_mul, mem_Ioo] using hq))).injOn


/-- Compactness supplies the strip constants required above. -/
theorem exists_uniform_smooth_inverse (eta : ℝ → ℝ) (lo hi a b : ℝ)
    (hab : a ≤ b) (hlo : lo < a) (hhi : b < hi)
    (heta : ∀ theta ∈ Icc lo hi, ContDiffAt ℝ ∞ eta theta) :
    ∃ H : ℝ, 0 < H ∧ ∀ p ∈ Icc a b ×ˢ Icc 0 H,
      intervalInverse eta lo hi p ∈ Ioo lo hi ∧
      intervalInverse eta lo hi p = p.1 + p.2 * eta (intervalInverse eta lo hi p) ∧
      ContDiffAt ℝ ∞ (intervalInverse eta lo hi) p := by
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (show ContinuousOn eta (Icc lo hi) from fun theta ht ↦
      (heta theta ht).continuousAt.continuousWithinAt)
  obtain ⟨K₀, hK₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (show ContinuousOn (deriv eta) (Icc lo hi) from fun theta ht ↦
      ((heta theta ht).derivWithin (m := 0) (by simp)).continuousAt.continuousWithinAt)
  let M := |M₀| + 1
  let K := |K₀| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨H₁, hH₁, hsmall₁⟩ := exists_pos_mul_lt (sub_pos.mpr hlo) M
  obtain ⟨H₂, hH₂, hsmall₂⟩ := exists_pos_mul_lt (sub_pos.mpr hhi) M
  obtain ⟨H₃, hH₃, hsmall₃⟩ := exists_pos_mul_lt (show (0 : ℝ) < 1 by norm_num) (2 * K)
  let H := min H₁ (min H₂ H₃)
  have hH : 0 < H := lt_min hH₁ (lt_min hH₂ hH₃)
  have h₁ : H ≤ H₁ := min_le_left _ _
  have h₂ : H ≤ H₂ := (min_le_right _ _).trans (min_le_left _ _)
  have h₃ : H ≤ H₃ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨H, hH, intervalInverse_strip eta lo hi a b H M K hab hlo hhi hH
    hM.le hK.le heta ?_ ?_ ?_ ?_ ?_⟩
  · intro theta ht
    have hh : |eta theta| ≤ M₀ := by simpa only [Real.norm_eq_abs] using hM₀ theta ht
    exact hh.trans (show M₀ ≤ M by dsimp [M]; linarith [le_abs_self M₀])
  · intro theta ht
    have hh : |deriv eta theta| ≤ K₀ := by simpa only [Real.norm_eq_abs] using hK₀ theta ht
    exact hh.trans (show K₀ ≤ K by dsimp [K]; linarith [le_abs_self K₀])
  · nlinarith [mul_le_mul_of_nonneg_right h₁ hM.le]
  · nlinarith [mul_le_mul_of_nonneg_right h₂ hM.le]
  · nlinarith [mul_le_mul_of_nonneg_right h₃ hK.le]


/-- A bounded phase derivative gives the precise inverse stability estimate. -/
theorem implicit_inverse_distance (eta : ℝ → ℝ) (lo hi K s h y theta : ℝ)
    (heta : ∀ x ∈ Icc lo hi, DifferentiableAt ℝ eta x)
    (hderiv : ∀ x ∈ Icc lo hi, |deriv eta x| ≤ K)
    (hy : y ∈ Icc lo hi) (htheta : theta ∈ Icc lo hi)
    (hh : 0 ≤ h) (hsmall : h * K ≤ 1 / 2)
    (heq : y = s + h * eta y) :
    |y - theta| ≤ 2 * |s - (theta - h * eta theta)| := by
  have hlip : |eta y - eta theta| ≤ K * |y - theta| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_deriv_le heta
        (fun x hx ↦ by simpa only [Real.norm_eq_abs] using hderiv x hx)
        (convex_Icc lo hi) htheta hy
  have he : y - theta = (s - (theta - h * eta theta)) + h * (eta y - eta theta) := by
    linear_combination heq
  have hb : |y - theta| ≤ |s - (theta - h * eta theta)| + h * K * |y - theta| := calc
    _ = |(s - (theta - h * eta theta)) + h * (eta y - eta theta)| := congrArg abs he
    _ ≤ |s - (theta - h * eta theta)| + |h * (eta y - eta theta)| := abs_add_le _ _
    _ = |s - (theta - h * eta theta)| + h * |eta y - eta theta| := by
      rw [abs_mul, abs_of_nonneg hh]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hlip hh]
  nlinarith [mul_le_mul_of_nonneg_right hsmall (abs_nonneg (y - theta))]

/-- The compact-strip inverse can simultaneously be chosen with stability
constant two against every angle in its defining interval. -/
theorem exists_uniform_smooth_lipschitz_inverse (eta : ℝ → ℝ) (lo hi a b : ℝ)
    (hab : a ≤ b) (hlo : lo < a) (hhi : b < hi)
    (heta : ∀ theta ∈ Icc lo hi, ContDiffAt ℝ ∞ eta theta) :
    ∃ H : ℝ, 0 < H ∧ ∀ p ∈ Icc a b ×ˢ Icc 0 H,
      intervalInverse eta lo hi p ∈ Ioo lo hi ∧
      intervalInverse eta lo hi p = p.1 + p.2 * eta (intervalInverse eta lo hi p) ∧
      ContDiffAt ℝ ∞ (intervalInverse eta lo hi) p ∧
      ∀ theta ∈ Icc lo hi,
        |intervalInverse eta lo hi p - theta| ≤ 2 * |p.1 - (theta - p.2 * eta theta)| ∧
        (theta - p.2 * eta theta < p.1 → theta < intervalInverse eta lo hi p) ∧
        (p.1 < theta - p.2 * eta theta → intervalInverse eta lo hi p < theta) := by
  obtain ⟨H, hH, hY⟩ := exists_uniform_smooth_inverse eta lo hi a b hab hlo hhi heta
  obtain ⟨K₀, hK₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (show ContinuousOn (deriv eta) (Icc lo hi) from fun theta ht ↦
      ((heta theta ht).derivWithin (m := 0) (by simp)).continuousAt.continuousWithinAt)
  let K := |K₀| + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hderiv : ∀ theta ∈ Icc lo hi, |deriv eta theta| ≤ K := by
    intro theta ht
    have hb : |deriv eta theta| ≤ K₀ := by simpa only [Real.norm_eq_abs] using hK₀ theta ht
    exact hb.trans (show K₀ ≤ K by dsimp [K]; linarith [le_abs_self K₀])
  obtain ⟨B, hB, hb⟩ := exists_pos_mul_lt (show (0 : ℝ) < 1 / 2 by norm_num) K
  refine ⟨min H B, lt_min hH hB, ?_⟩
  intro p hp
  have hpH : p ∈ Icc a b ×ˢ Icc 0 H := ⟨hp.1, hp.2.1, hp.2.2.trans (min_le_left _ _)⟩
  obtain ⟨hmem, heq, hsmooth⟩ := hY p hpH
  have hle : p.2 ≤ B := hp.2.2.trans (min_le_right _ _)
  have hsmall : p.2 * K ≤ 1 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hle hK.le]
  have hmono : StrictMonoOn (fun theta ↦ theta - p.2 * eta theta) (Icc lo hi) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro theta ht
      exact (continuousAt_id.sub ((heta theta ht).continuousAt.const_mul p.2)).continuousWithinAt
    · intro theta ht
      have ht' := interior_subset ht
      have hd := (hasDerivAt_id theta).sub
        (((heta theta ht').differentiableAt (by simp)).hasDerivAt.const_mul p.2)
      change 0 < deriv (id - fun y ↦ p.2 * eta y) theta
      rw [hd.deriv]
      have hdle : deriv eta theta ≤ K := (le_abs_self _).trans (hderiv theta ht')
      nlinarith [mul_le_mul_of_nonneg_left hdle hp.2.1]
  have hycc : intervalInverse eta lo hi p ∈ Icc lo hi := ⟨hmem.1.le, hmem.2.le⟩
  have heq' : intervalInverse eta lo hi p - p.2 * eta (intervalInverse eta lo hi p) = p.1 := by
    linarith
  refine ⟨hmem, heq, hsmooth, ?_⟩
  intro theta ht
  refine ⟨implicit_inverse_distance eta lo hi K p.1 p.2 _ theta
    (fun x hx ↦ (heta x hx).differentiableAt (by simp)) hderiv
    hycc ht hp.2.1 hsmall heq, ?_, ?_⟩
  · intro hlt
    apply (hmono.lt_iff_lt ht hycc).mp
    simpa only [heq'] using hlt
  · intro hlt
    apply (hmono.lt_iff_lt hycc ht).mp
    simpa only [heq'] using hlt

end MF21Quantization
#print axioms MF21Quantization.intervalInverse_contDiffAt

#print axioms MF21Quantization.intervalInverse_strip

#print axioms MF21Quantization.exists_uniform_smooth_inverse

#print axioms MF21Quantization.exists_uniform_smooth_lipschitz_inverse
