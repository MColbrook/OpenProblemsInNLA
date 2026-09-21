import MF21Restart.StableRootAlgebra
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! A concrete smooth extension and its exact first derivative at zero,
using the same quadratic-formula branch as manuscript Lemma 2. -/

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace MF21Restart

def stableRootCurve (κ : ℂ) (θ : ℝ) : ℂ :=
  stableQuadraticRoot (κ * (Real.sin (θ / 2) : ℂ))

lemma one_add_sq_mem_slitPlane (a : ℂ) (ha : a.re ≠ 0) :
    1 + a ^ 2 ∈ Complex.slitPlane := by
  by_cases hai : a.im = 0
  · left
    simp only [pow_two, Complex.add_re, Complex.one_re, Complex.mul_re, hai,
      zero_mul, sub_zero]
    nlinarith [sq_nonneg a.re]
  · right
    have him : (1 + a ^ 2).im = 2 * a.re * a.im := by
      simp only [pow_two, Complex.add_im, Complex.one_im, zero_add, Complex.mul_im]
      ring
    rw [him]
    exact mul_ne_zero (mul_ne_zero (by norm_num) ha) hai

lemma stableRootCurve_sqrt_argument_mem_slitPlane
    (κ : ℂ) (hκ : 0 < κ.re) (θ : ℝ) :
    1 + (κ * (Real.sin (θ / 2) : ℂ)) ^ 2 ∈ Complex.slitPlane := by
  by_cases hs : Real.sin (θ / 2) = 0
  · simp only [hs, Complex.ofReal_zero, mul_zero, zero_pow (by norm_num : 2 ≠ 0),
      add_zero]
    left
    norm_num
  · apply one_add_sq_mem_slitPlane
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero] using mul_ne_zero (ne_of_gt hκ) hs

set_option maxHeartbeats 1000000 in
theorem stableRootCurve_contDiff (κ : ℂ) (hκ : 0 < κ.re) :
    ContDiff ℝ ⊤ (stableRootCurve κ) := by
  have hs : ContDiff ℝ ⊤ (fun θ : ℝ => (Real.sin (θ / 2) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_sin.comp (contDiff_id.div_const 2))
  have hp : ContDiff ℝ ⊤ (fun θ : ℝ => κ * (Real.sin (θ / 2) : ℂ)) :=
    contDiff_const.mul hs
  have hi : ContDiff ℝ ⊤ (fun θ : ℝ => 1 + (κ * (Real.sin (θ / 2) : ℂ)) ^ 2) :=
    contDiff_const.add (hp.pow 2)
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  have hz := stableRootCurve_sqrt_argument_mem_slitPlane κ hκ θ
  have hout : ContDiffAt ℂ ⊤ Complex.sqrt
      (1 + (κ * (Real.sin (θ / 2) : ℂ)) ^ 2) :=
    (Complex.differentiableOn_sqrt.contDiffOn Complex.isOpen_slitPlane).contDiffAt
      (Complex.isOpen_slitPlane.mem_nhds hz)
  exact (((hout.restrict_scalars ℝ).comp θ hi.contDiffAt).sub hp.contDiffAt).pow 2

theorem stableQuadraticRoot_hasDerivAt_zero :
    HasDerivAt stableQuadraticRoot (-2) (0 : ℂ) := by
  have hi : HasDerivAt (fun a : ℂ => 1 + a ^ 2) 0 0 := by
    convert! ((hasDerivAt_id (0 : ℂ)).pow 2).const_add 1 using 1 <;> norm_num
  have hout : HasDerivAt Complex.sqrt (1 / 2 : ℂ) (1 + (0 : ℂ) ^ 2) := by
    have h := Complex.hasDerivAt_sqrt (z := 1) (by left; norm_num)
    simpa only [zero_pow (by norm_num : 2 ≠ 0), add_zero, Complex.one_cpow] using h
  have hs : HasDerivAt (fun a : ℂ => Complex.sqrt (1 + a ^ 2)) 0 0 := by
    simpa only [Function.comp_def, mul_zero] using hout.comp 0 hi
  convert! (hs.sub (hasDerivAt_id (0 : ℂ))).pow 2 using 1 <;>
    norm_num [stableQuadraticRoot]

theorem stableRootCurve_hasDerivAt_zero (κ : ℂ) :
    HasDerivAt (stableRootCurve κ) (-κ) (0 : ℝ) := by
  have hs : HasDerivAt (fun θ : ℝ => Real.sin (θ / 2)) (1 / 2) 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).div_const 2).sin using 1 <;> norm_num
  have hp : HasDerivAt (fun θ : ℝ => κ * (Real.sin (θ / 2) : ℂ)) (κ / 2) 0 := by
    convert! hs.ofReal_comp.const_mul κ using 1 <;> push_cast <;> ring
  have hout : HasDerivAt stableQuadraticRoot (-2)
      (κ * (Real.sin ((0 : ℝ) / 2) : ℂ)) := by
    simpa only [zero_div, Real.sin_zero, Complex.ofReal_zero, mul_zero] using
      stableQuadraticRoot_hasDerivAt_zero
  change HasDerivAt
    (fun θ : ℝ => stableQuadraticRoot (κ * (Real.sin (θ / 2) : ℂ))) (-κ) 0
  convert! hout.comp (0 : ℝ) hp using 1 <;> ring

theorem stableRootCurve_zero (κ : ℂ) : stableRootCurve κ 0 = 1 := by
  simp [stableRootCurve, stableQuadraticRoot_zero]

theorem stableRootCurve_ne_zero (κ : ℂ) (θ : ℝ) : stableRootCurve κ θ ≠ 0 :=
  stableQuadraticRoot_ne_zero _

theorem stableRootCurve_norm_lt_one (κ : ℂ) (hκ : 0 < κ.re)
    (θ : ℝ) (hθ : 0 < θ) (hθπ : θ ≤ Real.pi) : ‖stableRootCurve κ θ‖ < 1 := by
  apply stableQuadraticRoot_norm_lt_one
  have hs : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    using mul_pos hκ hs

theorem stableRootCurve_equation (κ : ℂ) (θ : ℝ) :
    2 - stableRootCurve κ θ - (stableRootCurve κ θ)⁻¹ =
      -4 * κ ^ 2 * (Real.sin (θ / 2) : ℂ) ^ 2 := by
  simpa only [stableRootCurve, mul_pow, mul_assoc] using
    stableQuadraticRoot_equation (κ * (Real.sin (θ / 2) : ℂ))

#print axioms stableRootCurve_contDiff
#print axioms stableRootCurve_hasDerivAt_zero
#print axioms stableRootCurve_norm_lt_one
#print axioms stableRootCurve_equation

end MF21Restart
