import MF21.PhaseRotatedError
import Mathlib.Analysis.Calculus.MeanValue

/-! Real error bounds, including the endpoint-sensitive estimate. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Topology ContDiff
open Set
namespace MF21ActualBoundary
open MF21Bulk

def realError (m : ℕ) (hm : 0<m) (d : SlopeData m) (eta : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (complexError m hm d eta n x).re

theorem complexError_smooth (m : ℕ) (hm : 0<m) (d : SlopeData m)
    (eta : ℝ → ℝ) (n : ℕ) (x : ℝ) (hx : x ∈ Icc 0 Real.pi)
    (he : ContDiffAt ℝ ∞ eta x) : ContDiffAt ℝ ∞ (complexError m hm d eta n) x := by
  unfold complexError phaseRotate
  apply ContDiffAt.mul
  · apply contDiffAt_const.mul
    apply unitRoot_contDiff.contDiffAt.comp x
    exact ((contDiffAt_const.mul contDiffAt_id).sub he).neg
  · exact normalizedRemainder_smooth m hm d (n+m) x hx

theorem realError_smooth (m : ℕ) (hm : 0<m) (d : SlopeData m)
    (eta : ℝ → ℝ) (n : ℕ) (x : ℝ) (hx : x ∈ Icc 0 Real.pi)
    (he : ContDiffAt ℝ ∞ eta x) : ContDiffAt ℝ ∞ (realError m hm d eta n) x :=
  Complex.reCLM.contDiff.contDiffAt.comp x (complexError_smooth m hm d eta n x hx he)

theorem realError_bounds (m : ℕ) (hm : 0<m) (d : SlopeData m)
    (eta : ℝ → ℝ) (he : ∀ x ∈ Icc 0 Real.pi, ContDiffAt ℝ ∞ eta x) :
    ∃ c : ℝ, 0<c ∧ ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, ∀ x ∈ Ioc 0 Real.pi,
      |realError m hm d eta n x| ≤ C*Real.exp (-c*n*x) ∧
      |deriv (realError m hm d eta n) x| ≤ C*(n+1)*Real.exp (-c*n*x) := by
  obtain ⟨c,hc,C,hC,hbound⟩ := complexError_bounds m hm d eta he
  refine ⟨c,hc,C,hC,?_⟩
  intro n x hx
  have hx' : x ∈ Icc 0 Real.pi := ⟨hx.1.le,hx.2⟩
  obtain ⟨hb,hbd⟩ := hbound n x hx
  constructor
  · exact (Complex.abs_re_le_norm _).trans hb
  · have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
      ((complexError_smooth m hm d eta n x hx' (he x hx')).differentiableAt (by simp)).hasDerivAt
    have hde : deriv (realError m hm d eta n) x =
        (deriv (complexError m hm d eta n) x).re := hd.deriv
    rw [hde]
    exact (Complex.abs_re_le_norm _).trans hbd

/-- Vanishing at pi converts a uniform derivative estimate into the bound
that excludes the artificial endpoint zero. -/
theorem endpoint_sensitive_error_bound (E : ℝ → ℝ) (n : ℕ) (c C : ℝ)
    (hc : 0<c) (hC : 0≤C)
    (he : ∀ x ∈ Icc (Real.pi/2) Real.pi, DifferentiableAt ℝ E x)
    (hd : ∀ x ∈ Icc (Real.pi/2) Real.pi,
      |deriv E x| ≤ C*(n+1)*Real.exp (-c*n*x)) (hpi : E Real.pi=0)
    (x : ℝ) (hx : x ∈ Icc (Real.pi/2) Real.pi) :
    |E x| ≤ C*(n+1)*(Real.pi-x)*Real.exp (-c*n*Real.pi/2) := by
  have hlocal : ∀ t ∈ Icc x Real.pi,
      ‖deriv E t‖ ≤ C*(n+1)*Real.exp (-c*n*Real.pi/2) := by
    intro t ht
    apply (hd t ⟨hx.1.trans ht.1,ht.2⟩).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hcn : 0≤c*(n : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (hx.1.trans ht.1) hcn]
  have hdiff : ∀ t ∈ Icc x Real.pi, DifferentiableAt ℝ E t :=
    fun t ht => he t ⟨hx.1.trans ht.1,ht.2⟩
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hlocal (convex_Icc _ _)
    (show Real.pi ∈ Icc x Real.pi from ⟨hx.2,le_rfl⟩)
    (show x ∈ Icc x Real.pi from ⟨le_rfl,hx.2⟩)
  rw [hpi, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr hx.2)] at h
  nlinarith [h]

end MF21ActualBoundary
#print axioms MF21ActualBoundary.realError_bounds
#print axioms MF21ActualBoundary.endpoint_sensitive_error_bound
