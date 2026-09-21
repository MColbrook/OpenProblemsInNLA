import MF21Restart.StableRootSmooth
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! The individual phase extends smoothly through zero. The phase remains
the sum of individual arguments later, never the argument of a product. -/

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace MF21Restart

def phaseNormalized (κ : ℂ) (θ : ℝ) : ℂ :=
  Complex.exp (-(θ : ℂ) * Complex.I) *
    (κ * Complex.sqrt (1 + (κ * (Real.sin (θ / 2) : ℂ)) ^ 2) +
      Complex.I * (Real.cos (θ / 2) : ℂ) -
      (1 + κ ^ 2) * (Real.sin (θ / 2) : ℂ))

def individualPhase (κ : ℂ) (θ : ℝ) : ℝ := (phaseNormalized κ θ).arg

theorem phase_factorization (κ : ℂ) (θ : ℝ) :
    1 - stableRootCurve κ θ * Complex.exp (-(θ : ℂ) * Complex.I) =
      (2 * (Real.sin (θ / 2) : ℂ)) * phaseNormalized κ θ := by
  have hz : Complex.exp (-(θ : ℂ) * Complex.I) *
      Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    convert! Complex.exp_zero using 1 <;> congr 1 <;> ring
  have hcos := Real.cos_two_mul_eq_one_sub (θ / 2)
  have hsin := Real.sin_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at hcos hsin
  have hb := complex_sqrt_sq (1 + (κ * (Real.sin (θ / 2) : ℂ)) ^ 2)
  unfold phaseNormalized stableRootCurve stableQuadraticRoot
  calc
    1 - (Complex.sqrt (1 + (κ * (Real.sin (θ / 2) : ℂ)) ^ 2) -
        κ * (Real.sin (θ / 2) : ℂ)) ^ 2 *
        Complex.exp (-(θ : ℂ) * Complex.I) =
      Complex.exp (-(θ : ℂ) * Complex.I) *
        (Complex.exp ((θ : ℂ) * Complex.I) -
          (Complex.sqrt (1 + (κ * (Real.sin (θ / 2) : ℂ)) ^ 2) -
            κ * (Real.sin (θ / 2) : ℂ)) ^ 2) := by
      rw [mul_sub, hz]
      ring
    _ = _ := by
      rw [Complex.exp_ofReal_mul_I, hcos, hsin]
      push_cast at hb ⊢
      linear_combination -(Complex.exp (-(θ : ℂ) * Complex.I)) * hb

theorem phaseNormalized_zero (κ : ℂ) : phaseNormalized κ 0 = κ + Complex.I := by
  simp [phaseNormalized, Complex.sqrt]

set_option maxHeartbeats 1000000 in
theorem phaseNormalized_contDiff (κ : ℂ) (hκ : 0 < κ.re) :
    ContDiff ℝ ⊤ (phaseNormalized κ) := by
  have hs : ContDiff ℝ ⊤ (fun θ : ℝ => (Real.sin (θ / 2) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_sin.comp (contDiff_id.div_const 2))
  have hc : ContDiff ℝ ⊤ (fun θ : ℝ => (Real.cos (θ / 2) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_cos.comp (contDiff_id.div_const 2))
  have hi : ContDiff ℝ ⊤ (fun θ : ℝ => 1 + (κ * (Real.sin (θ / 2) : ℂ)) ^ 2) :=
    contDiff_const.add ((contDiff_const.mul hs).pow 2)
  have hb : ContDiff ℝ ⊤
      (fun θ : ℝ => Complex.sqrt (1 + (κ * (Real.sin (θ / 2) : ℂ)) ^ 2)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro θ
    have hz := stableRootCurve_sqrt_argument_mem_slitPlane κ hκ θ
    have hout : ContDiffAt ℂ ⊤ Complex.sqrt
        (1 + (κ * (Real.sin (θ / 2) : ℂ)) ^ 2) :=
      (Complex.differentiableOn_sqrt.contDiffOn Complex.isOpen_slitPlane).contDiffAt
        (Complex.isOpen_slitPlane.mem_nhds hz)
    exact (hout.restrict_scalars ℝ).comp θ hi.contDiffAt
  have he : ContDiff ℝ ⊤ (fun θ : ℝ => Complex.exp (-(θ : ℂ) * Complex.I)) :=
    ((Complex.contDiff_exp : ContDiff ℂ ⊤ Complex.exp).restrict_scalars ℝ).comp
      (Complex.ofRealCLM.contDiff.neg.mul contDiff_const)
  exact he.mul (((contDiff_const.mul hb).add (contDiff_const.mul hc)).sub
    (contDiff_const.mul hs))

theorem phaseNormalized_re_pos (κ : ℂ) (hκ : 0 < κ.re)
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi) : 0 < (phaseNormalized κ θ).re := by
  rcases eq_or_lt_of_le hθ.1 with hzero | hpos
  · subst θ
    simpa [phaseNormalized_zero] using hκ
  have hs : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos, hθ.2])
  have he : ‖Complex.exp (-(θ : ℂ) * Complex.I)‖ = 1 := by
    simpa only [Complex.ofReal_neg] using Complex.norm_exp_ofReal_mul_I (-θ)
  have hr := stableRootCurve_norm_lt_one κ hκ θ hpos hθ.2
  have hprod : (stableRootCurve κ θ * Complex.exp (-(θ : ℂ) * Complex.I)).re < 1 := by
    calc
      _ ≤ ‖stableRootCurve κ θ * Complex.exp (-(θ : ℂ) * Complex.I)‖ :=
        Complex.re_le_norm _
      _ = ‖stableRootCurve κ θ‖ := by rw [norm_mul, he, mul_one]
      _ < 1 := hr
  have hid := congrArg Complex.re (phase_factorization κ θ)
  have hscalar :
      ((2 * (Real.sin (θ / 2) : ℂ)) * phaseNormalized κ θ).re =
        (2 * Real.sin (θ / 2)) * (phaseNormalized κ θ).re := by
    rw [show 2 * (Real.sin (θ / 2) : ℂ) = ((2 * Real.sin (θ / 2) : ℝ) : ℂ) by
      simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  rw [Complex.sub_re, Complex.one_re, hscalar] at hid
  nlinarith

theorem individualPhase_eq_original (κ : ℂ) (θ : ℝ)
    (hθ : 0 < θ) (hθπ : θ ≤ Real.pi) :
    individualPhase κ θ =
      (1 - stableRootCurve κ θ * Complex.exp (-(θ : ℂ) * Complex.I)).arg := by
  have hs : 0 < 2 * Real.sin (θ / 2) := mul_pos (by norm_num)
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  rw [phase_factorization]
  simpa only [individualPhase, Complex.ofReal_mul, Complex.ofReal_ofNat] using
    (Complex.arg_real_mul (phaseNormalized κ θ) hs).symm

theorem individualPhase_contDiffAt (κ : ℂ) (hκ : 0 < κ.re)
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi) :
    ContDiffAt ℝ ⊤ (individualPhase κ) θ := by
  change ContDiffAt ℝ ⊤ (fun t : ℝ => (phaseNormalized κ t).arg) θ
  have hz : phaseNormalized κ θ ∈ Complex.slitPlane :=
    Or.inl (phaseNormalized_re_pos κ hκ θ hθ)
  have hlog : ContDiffAt ℝ ⊤ (fun t : ℝ => Complex.log (phaseNormalized κ t)) θ :=
    (Complex.contDiffAt_log hz |>.restrict_scalars ℝ).comp θ
      (phaseNormalized_contDiff κ hκ).contDiffAt
  simpa only [Function.comp_def, Complex.imCLM_apply, Complex.log_im] using
    Complex.imCLM.contDiff.contDiffAt.comp θ hlog

#print axioms phase_factorization
#print axioms phaseNormalized_zero
#print axioms phaseNormalized_contDiff
#print axioms phaseNormalized_re_pos
#print axioms individualPhase_eq_original
#print axioms individualPhase_contDiffAt

end MF21Restart
