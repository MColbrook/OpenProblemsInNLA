import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace MF21Restart

theorem analyticAt_dslope_zero (f : ℝ → ℂ) (hf : AnalyticAt ℝ f 0) :
    AnalyticAt ℝ (dslope f 0) 0 := by
  obtain ⟨F, hFa, hF⟩ := hf.exists_eq_sum_add_pow_mul 1
  have hfac : ∀ z : ℝ, f z = f 0 + z • F z := by
    intro z
    simpa using hF z
  have hder : HasDerivAt (fun z : ℝ => f 0 + z • F z) (F 0) 0 := by
    convert! (((hasDerivAt_id (0 : ℝ)).smul hFa.differentiableAt.hasDerivAt).const_add (f 0))
      using 1 <;> simp
  have hdf : HasDerivAt f (F 0) 0 :=
    hder.congr_of_eventuallyEq (Filter.Eventually.of_forall hfac)
  have heq : dslope f 0 = F := by
    funext z
    by_cases hz : z = 0
    · subst z
      rw [dslope_same, hdf.deriv]
    · rw [dslope_of_ne f hz, slope_def_module, sub_zero, hfac z,
        add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hz, one_smul]
  rw [heq]
  exact hFa

theorem analyticAt_dslope_of_forall_analyticAt
    (f : ℝ → ℂ) (hf : ∀ x : ℝ, AnalyticAt ℝ f x) (x : ℝ) :
    AnalyticAt ℝ (dslope f 0) x := by
  by_cases hx : x = 0
  · subst x
    exact analyticAt_dslope_zero f (hf 0)
  · have h : AnalyticAt ℝ (fun z : ℝ => z⁻¹ • (f z - f 0)) x :=
      (analyticAt_id.inv hx).smul ((hf x).sub analyticAt_const)
    have hs : AnalyticAt ℝ (slope f 0) x := by
      simpa only [slope_fun_def, sub_zero, vsub_eq_sub] using h
    exact hs.congr (dslope_eventuallyEq_slope_of_ne f hx).symm

#print axioms analyticAt_dslope_zero
#print axioms analyticAt_dslope_of_forall_analyticAt

end MF21Restart
