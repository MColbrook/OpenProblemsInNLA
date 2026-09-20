import MF21.Definitions
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! Smooth inversion of the phase quantization equation Y = s + h eta(Y). -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency.types false
namespace MF21Quantization

def equation (eta : ℝ → ℝ) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  p.2 - p.1.1 - p.1.2 * eta p.2

def equationDerivative (eta : ℝ → ℝ) (s : ℝ) : ((ℝ × ℝ) × ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ -
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ) -
    eta s • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)

theorem equation_hasFDerivAt (eta : ℝ → ℝ) (s : ℝ)
    (he : DifferentiableAt ℝ eta s) :
    HasFDerivAt (equation eta) (equationDerivative eta s) ((s, 0), s) := by
  have hy : HasFDerivAt (fun p : (ℝ × ℝ) × ℝ ↦ p.2)
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ) ((s, 0), s) := hasFDerivAt_snd
  have hp : HasFDerivAt (fun p : (ℝ × ℝ) × ℝ ↦ p.1)
      (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ) ((s, 0), s) := hasFDerivAt_fst
  have heta := he.hasFDerivAt.comp ((s, (0 : ℝ)), s) hy
  have hmul := hp.snd.mul heta
  have hsub := (hy.sub hp.fst).sub hmul
  simpa only [equation, equationDerivative, Function.comp_def, Prod.fst, Prod.snd,
    zero_smul, zero_add] using! hsub

theorem equation_contDiffAt (eta : ℝ → ℝ) (s : ℝ)
    (he : ContDiffAt ℝ ∞ eta s) : ContDiffAt ℝ ∞ (equation eta) ((s, 0), s) := by
  unfold equation
  exact (contDiffAt_snd.sub contDiffAt_fst.fst).sub
    (contDiffAt_fst.snd.mul (he.comp _ contDiffAt_snd))

theorem equation_partial_identity (eta : ℝ → ℝ) (s : ℝ)
    (he : DifferentiableAt ℝ eta s) :
    (fderiv ℝ (equation eta) ((s, 0), s)).comp
      (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ) = ContinuousLinearMap.id ℝ ℝ := by
  rw [(equation_hasFDerivAt eta s he).fderiv]
  ext y
  simp [equationDerivative]

/-- Local smooth implicit inversion at every point of the zero-step slice. -/
theorem exists_local_smooth_inverse (eta : ℝ → ℝ) (s : ℝ)
    (he : ContDiffAt ℝ ∞ eta s) :
    ∃ Y : ℝ × ℝ → ℝ, Y (s, 0) = s ∧ ContDiffAt ℝ ∞ Y (s, 0) ∧
      ∀ᶠ p in 𝓝 (s, (0 : ℝ)), Y p = p.1 + p.2 * eta (Y p) := by
  have hc := equation_contDiffAt eta s he
  have hi : ((fderiv ℝ (equation eta) ((s, 0), s)).comp
      (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ)).IsInvertible := by
    rw [equation_partial_identity eta s (he.differentiableAt (by simp))]
    exact ⟨ContinuousLinearEquiv.refl ℝ ℝ, rfl⟩
  let Y := hc.implicitFunction (by simp) hi
  refine ⟨Y, hc.implicitFunction_apply_self (by simp) hi,
    hc.contDiffAt_implicitFunction (by simp) hi, ?_⟩
  filter_upwards [hc.eventually_apply_implicitFunction (by simp) hi] with p hp
  change equation eta (p, Y p) = equation eta ((s, 0), s) at hp
  simp only [equation, zero_mul, sub_self, sub_zero] at hp
  linarith

/-- Along s = c h, the implicit inverse has the exact first-order shift eta(0). -/
theorem inverse_diagonal_profile (eta : ℝ → ℝ) (Y : ℝ × ℝ → ℝ)
    (heta : ContinuousAt eta 0) (hY : ContinuousAt Y (0, 0)) (hY0 : Y (0, 0) = 0)
    (heq : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)), Y p = p.1 + p.2 * eta (Y p))
    (c : ℝ) (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (hne : ∀ᶠ n in atTop, h n ≠ 0) :
    Tendsto (fun n ↦ Y (c * h n, h n) / h n) atTop (𝓝 (c + eta 0)) := by
  have hp : Tendsto (fun n ↦ (c * h n, h n)) atTop (𝓝 ((0 : ℝ), (0 : ℝ))) := by
    simpa only [mul_zero] using (hh.const_mul c).prodMk_nhds hh
  have hy : Tendsto (fun n ↦ Y (c * h n, h n)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hY0, Function.comp_def] using hY.tendsto.comp hp
  have ht := (heta.tendsto.comp hy).const_add c
  apply ht.congr'
  filter_upwards [hp.eventually heq, hne] with n he hn
  change c + eta (Y (c * h n, h n)) = Y (c * h n, h n) / h n
  rw [eq_div_iff hn]
  linear_combination -he

theorem sin_eq_mul_sinc (x : ℝ) : Real.sin x = x * Real.sinc x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero hx]
    field_simp

/-- The exact symbol has leading power profile under any rescaled angle limit. -/
theorem symbol_scaled_tendsto (m : ℕ) (theta h : ℕ → ℝ) (c : ℝ)
    (htheta : Tendsto theta atTop (𝓝 0))
    (hratio : Tendsto (fun n ↦ theta n / h n) atTop (𝓝 c)) :
    Tendsto (fun n ↦ MF21Challenge.symbol m (theta n) / (h n) ^ (2 * m))
      atTop (𝓝 (c ^ (2 * m))) := by
  have hsinc : Tendsto (fun n ↦ Real.sinc (theta n / 2)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [zero_div, Real.sinc_zero, Function.comp_def] using
      (Real.continuous_sinc.tendsto (0 / 2)).comp (htheta.div_const 2)
  have ht := (hsinc.mul hratio).pow (2 * m)
  simp only [one_mul] at ht
  convert ht using 1
  funext n
  rw [MF21Challenge.symbol, ← div_pow, sin_eq_mul_sinc]
  congr 1
  ring

/-- Fixed-index leading eigenvalue profile for any local smooth implicit inverse. -/
theorem implicit_symbol_diagonal_profile (m : ℕ) (eta : ℝ → ℝ) (Y : ℝ × ℝ → ℝ)
    (heta : ContinuousAt eta 0) (hY : ContinuousAt Y (0, 0)) (hY0 : Y (0, 0) = 0)
    (heq : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)), Y p = p.1 + p.2 * eta (Y p))
    (c : ℝ) (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (hne : ∀ᶠ n in atTop, h n ≠ 0) :
    Tendsto (fun n ↦ MF21Challenge.symbol m (Y (c * h n, h n)) / (h n) ^ (2 * m))
      atTop (𝓝 ((c + eta 0) ^ (2 * m))) := by
  have hp : Tendsto (fun n ↦ (c * h n, h n)) atTop (𝓝 ((0 : ℝ), (0 : ℝ))) := by
    simpa only [mul_zero] using (hh.const_mul c).prodMk_nhds hh
  have hy : Tendsto (fun n ↦ Y (c * h n, h n)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hY0, Function.comp_def] using hY.tendsto.comp hp
  exact symbol_scaled_tendsto m _ h _ hy
    (inverse_diagonal_profile eta Y heta hY hY0 heq c h hh hne)

end MF21Quantization
#print axioms MF21Quantization.exists_local_smooth_inverse

#print axioms MF21Quantization.implicit_symbol_diagonal_profile
