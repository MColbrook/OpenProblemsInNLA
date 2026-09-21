import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
Uniform scalar implicit inversion on a compact interval. A root is
constructed by the intermediate value theorem and proved unique before
the local implicit-function theorem is used to establish regularity of
the same function on the whole rectangle. The analytic order `⊤` is
Mathlib's omega, not its C-infinity order. The statement was locked in
`UNIFORM_IMPLICIT_PHASE_STATEMENTS.md` before this source was written.
-/

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace MF21Restart

/-- One jointly analytic solution of `y=x+h*eta(y)` on a uniform open
rectangle around a closed interval, with a quantitative displacement
bound and uniqueness on a fixed enlarged closed interval. -/
theorem uniform_implicit_scalar
    (η : ℝ → ℝ) (L r C : ℝ) (hL : 0 ≤ L) (hr : 0 < r) (hC : 0 < C)
    (hη : ∀ y ∈ Set.Icc (-r) (L + r),
      ContDiffAt ℝ ⊤ η y ∧ |η y| ≤ C ∧ |deriv η y| ≤ C) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Y : ℝ × ℝ → ℝ,
      let D := Set.Ioo (-r / 2) (L + r / 2) ×ˢ Set.Ioo (-ε) ε
      (∀ p ∈ D, ContDiffAt ℝ ⊤ Y p) ∧
      (∀ p ∈ D, Y p ∈ Set.Ioo (-r) (L + r) ∧
        Y p = p.1 + p.2 * η (Y p) ∧ |Y p - p.1| ≤ C * |p.2|) ∧
      (∀ x ∈ Set.Ioo (-r / 2) (L + r / 2), Y (x, 0) = x) ∧
      (∀ p ∈ D, ∀ y ∈ Set.Icc (-r) (L + r),
        y = p.1 + p.2 * η y → y = Y p) := by
  classical
  let ε : ℝ := min (r / 4) (1 / 2) / C
  have hε : 0 < ε := div_pos (lt_min (by positivity) (by norm_num)) hC
  have hεC : ε * C = min (r / 4) (1 / 2) := by
    dsimp [ε]
    exact div_mul_cancel₀ _ hC.ne'
  have hsmall (h : ℝ) (hh : |h| < ε) :
      |h| * C < r / 4 ∧ |h| * C < 1 / 2 := by
    have hb : |h| * C < min (r / 4) (1 / 2) := by
      rw [← hεC]
      exact mul_lt_mul_of_pos_right hh hC
    exact ⟨hb.trans_le (min_le_left _ _), hb.trans_le (min_le_right _ _)⟩
  let D : Set (ℝ × ℝ) :=
    Set.Ioo (-r / 2) (L + r / 2) ×ˢ Set.Ioo (-ε) ε
  have hDopen : IsOpen D := isOpen_Ioo.prod isOpen_Ioo
  have hinterval : -r ≤ L + r := by linarith
  have hderiv (h y : ℝ) (hy : y ∈ Set.Icc (-r) (L + r)) :
      HasDerivAt (fun z : ℝ => z - h * η z) (1 - h * deriv η y) y := by
    exact (hasDerivAt_id y).sub
      (((hη y hy).1.differentiableAt (by simp)).hasDerivAt.const_mul h)
  have hpartial_pos (h y : ℝ) (hh : |h| < ε)
      (hy : y ∈ Set.Icc (-r) (L + r)) : 0 < 1 - h * deriv η y := by
    have habs : |h * deriv η y| ≤ |h| * C := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hη y hy).2.2 (abs_nonneg h)
    have hless := (hsmall h hh).2
    have hle := le_abs_self (h * deriv η y)
    linarith
  have hmono (h : ℝ) (hh : |h| < ε) :
      StrictMonoOn (fun y : ℝ => y - h * η y) (Set.Icc (-r) (L + r)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro y hy
      exact (hderiv h y hy).continuousAt.continuousWithinAt
    · intro y hy
      have hym : y ∈ Set.Icc (-r) (L + r) :=
        Set.mem_of_mem_of_subset hy interior_subset
      rw [(hderiv h y hym).deriv]
      exact hpartial_pos h y hh hym
  have hex (p : ℝ × ℝ) (hp : p ∈ D) :
      ∃! y : ℝ, y ∈ Set.Icc (-r) (L + r) ∧ y = p.1 + p.2 * η y := by
    have hh : |p.2| < ε := abs_lt.mpr hp.2
    have hc : ContinuousOn (fun y : ℝ => y - p.2 * η y)
        (Set.Icc (-r) (L + r)) := by
      intro y hy
      exact (hderiv p.2 y hy).continuousAt.continuousWithinAt
    have hleft : -r - p.2 * η (-r) < p.1 := by
      have habs : |p.2 * η (-r)| < r / 4 := by
        calc
          _ = |p.2| * |η (-r)| := abs_mul _ _
          _ ≤ |p.2| * C := mul_le_mul_of_nonneg_left
            (hη (-r) ⟨le_rfl, hinterval⟩).2.1 (abs_nonneg _)
          _ < r / 4 := (hsmall p.2 hh).1
      have hb := abs_lt.mp habs
      linarith [hp.1.1]
    have hright : p.1 < L + r - p.2 * η (L + r) := by
      have habs : |p.2 * η (L + r)| < r / 4 := by
        calc
          _ = |p.2| * |η (L + r)| := abs_mul _ _
          _ ≤ |p.2| * C := mul_le_mul_of_nonneg_left
            (hη (L + r) ⟨hinterval, le_rfl⟩).2.1 (abs_nonneg _)
          _ < r / 4 := (hsmall p.2 hh).1
      have hb := abs_lt.mp habs
      linarith [hp.1.2]
    obtain ⟨y, hy, heq⟩ := intermediate_value_Icc hinterval hc ⟨hleft.le, hright.le⟩
    have heq' : y = p.1 + p.2 * η y := by
      change y - p.2 * η y = p.1 at heq
      linarith
    refine ⟨y, ⟨hy, heq'⟩, ?_⟩
    intro z hz
    apply (hmono p.2 hh).injOn hz.1 hy
    linarith only [hz.2, heq']
  let Y : ℝ × ℝ → ℝ := fun p =>
    if hp : p ∈ D then (hex p hp).choose else p.1
  have hY (p : ℝ × ℝ) (hp : p ∈ D) :
      Y p ∈ Set.Icc (-r) (L + r) ∧ Y p = p.1 + p.2 * η (Y p) := by
    dsimp only [Y]
    rw [dif_pos hp]
    exact (hex p hp).choose_spec.1
  have hunique (p : ℝ × ℝ) (hp : p ∈ D) (y : ℝ)
      (hy : y ∈ Set.Icc (-r) (L + r)) (heq : y = p.1 + p.2 * η y) : y = Y p :=
    (hex p hp).unique ⟨hy, heq⟩ (hY p hp)
  have hsize (p : ℝ × ℝ) (hp : p ∈ D) : |Y p - p.1| ≤ C * |p.2| := by
    have heq : Y p - p.1 = p.2 * η (Y p) := by linarith only [(hY p hp).2]
    rw [heq, abs_mul, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hη (Y p) (hY p hp).1).2.1 (abs_nonneg _)
  have hinterior (p : ℝ × ℝ) (hp : p ∈ D) : Y p ∈ Set.Ioo (-r) (L + r) := by
    have hdist : |Y p - p.1| < r / 4 := by
      exact (hsize p hp).trans_lt (by simpa only [mul_comm] using
        (hsmall p.2 (abs_lt.mpr hp.2)).1)
    have hb := abs_lt.mp hdist
    constructor <;> linarith [hp.1.1, hp.1.2]
  refine ⟨ε, hε, Y, ?_, ?_, ?_, ?_⟩
  · intro p hp
    change p ∈ D at hp
    let F : (ℝ × ℝ) × ℝ → ℝ := fun u => u.2 - u.1.1 - u.1.2 * η u.2
    have hcd : ContDiffAt ℝ ⊤ F (p, Y p) := by
      have he : ContDiffAt ℝ ⊤ (fun u : (ℝ × ℝ) × ℝ => η u.2) (p, Y p) :=
        (hη (Y p) (hY p hp).1).1.comp (p, Y p) contDiffAt_snd
      exact (contDiffAt_snd.sub contDiffAt_fst.fst).sub (contDiffAt_fst.snd.mul he)
    let s : ℝ := 1 - p.2 * deriv η (Y p)
    have hs : 0 < s := hpartial_pos p.2 (Y p) (abs_lt.mpr hp.2) (hY p hp).1
    have hslice : HasDerivAt (fun y : ℝ => F (p, y)) s (Y p) := by
      exact ((hasDerivAt_id (Y p)).sub_const p.1).sub
        (((hη (Y p) (hY p hp).1).1.differentiableAt (by simp)).hasDerivAt.const_mul p.2)
    have hcomp : HasFDerivAt (fun y : ℝ => F (p, y))
        ((fderiv ℝ F (p, Y p)).comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ)) (Y p) :=
      (hcd.differentiableAt (by simp)).hasFDerivAt.comp (Y p)
        (hasFDerivAt_prodMk_right p (Y p))
    have hpartial : (fderiv ℝ F (p, Y p)).comp
        (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ) = ContinuousLinearMap.toSpanSingleton ℝ s :=
      hcomp.unique hslice.hasFDerivAt
    have hinv : ((fderiv ℝ F (p, Y p)).comp
        (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ)).IsInvertible := by
      rw [hpartial]
      refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 s hs.ne'), ?_⟩
      ext z
      simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.unitsEquivAut_apply,
        Units.val_mk0, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    let φ : ℝ × ℝ → ℝ := hcd.implicitFunction (by simp) hinv
    have hφself : φ p = Y p := hcd.implicitFunction_apply_self (by simp) hinv
    have hφcd : ContDiffAt ℝ ⊤ φ p := hcd.contDiffAt_implicitFunction (by simp) hinv
    have hφeq : ∀ᶠ q in 𝓝 p, F (q, φ q) = F (p, Y p) :=
      hcd.eventually_apply_implicitFunction (by simp) hinv
    have hFzero : F (p, Y p) = 0 := by
      dsimp only [F]
      linarith only [(hY p hp).2]
    have hφmem : ∀ᶠ q in 𝓝 p, φ q ∈ Set.Ioo (-r) (L + r) :=
      hφcd.continuousAt.eventually_mem
        (isOpen_Ioo.mem_nhds (by rw [hφself]; exact hinterior p hp))
    have hagree : Y =ᶠ[𝓝 p] φ := by
      filter_upwards [hDopen.mem_nhds hp, hφmem, hφeq] with q hq hyq heq
      have heq' : φ q = q.1 + q.2 * η (φ q) := by
        rw [hFzero] at heq
        change φ q - q.1 - q.2 * η (φ q) = 0 at heq
        linarith
      exact (hunique q hq (φ q) ⟨hyq.1.le, hyq.2.le⟩ heq').symm
    exact hφcd.congr_of_eventuallyEq hagree
  · intro p hp
    exact ⟨hinterior p hp, (hY p hp).2, hsize p hp⟩
  · intro x hx
    have hp : (x, 0) ∈ D := ⟨hx, by constructor <;> linarith⟩
    simpa only [zero_mul, add_zero] using (hY (x, 0) hp).2
  · exact hunique

#print axioms uniform_implicit_scalar

end MF21Restart
