import MF21Restart.StableRootSmooth
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.Order.Compact

/-!
The compactness argument behind manuscript (6), for the actual root curve.
The difference quotient is extended by the actual derivative at zero; its
negative maximum gives a positive linear gap and hence exponential decay.
STABLE_ROOT_DECAY_STATEMENTS.md fixes the statements before this proof.
-/

set_option autoImplicit false
noncomputable section
open Set

namespace MF21Restart

/-- A negative endpoint derivative and a strict compact-interval gap yield
a uniform positive linear gap from the endpoint value. -/
theorem exists_pos_linear_upper_bound_of_neg_deriv
    (f : ℝ → ℝ) (L d : ℝ) (hL : 0 < L)
    (hf : ContinuousOn f (Set.Icc 0 L)) (hf0 : f 0 = 1)
    (hd : HasDerivAt f d 0) (hdneg : d < 0)
    (hlt : ∀ x : ℝ, 0 < x → x ≤ L → f x < 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ x : ℝ, 0 ≤ x → x ≤ L → f x ≤ 1 - c * x := by
  have hscont : ContinuousOn (dslope f 0) (Icc 0 L) := by
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      exact (continuousAt_dslope_same.mpr hd.differentiableAt).continuousWithinAt
    · exact (continuousWithinAt_dslope_of_ne hx0).mpr (hf x hx)
  have hsneg : ∀ x ∈ Icc 0 L, dslope f 0 x < 0 := by
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      simpa only [dslope_same, hd.deriv] using hdneg
    · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
      have hprod : x * dslope f 0 x = f x - 1 := by
        simpa only [sub_zero, smul_eq_mul, hf0] using sub_smul_dslope f 0 x
      have hfx : f x < 1 := hlt x hxpos hx.2
      by_contra hn
      have hnonneg : 0 ≤ x * dslope f 0 x :=
        mul_nonneg hx.1 (le_of_not_gt hn)
      linarith
  obtain ⟨x₀, hx₀, hmax⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) L)).exists_isMaxOn
      ⟨0, le_rfl, hL.le⟩ hscont
  refine ⟨-dslope f 0 x₀, neg_pos.mpr (hsneg x₀ hx₀), ?_⟩
  intro x hx hxL
  have hprod : x * dslope f 0 x = f x - 1 := by
    simpa only [sub_zero, smul_eq_mul, hf0] using sub_smul_dslope f 0 x
  have hmul : x * dslope f 0 x ≤ x * dslope f 0 x₀ :=
    mul_le_mul_of_nonneg_left ((isMaxOn_iff.mp hmax) x ⟨hx, hxL⟩) hx
  calc
    f x = 1 + x * dslope f 0 x := by linarith
    _ ≤ 1 + x * dslope f 0 x₀ := by linarith
    _ = 1 - (-dslope f 0 x₀) * x := by ring

/-- The uniform linear gap implies the corresponding exponential bound. -/
theorem exists_pos_exp_upper_bound_of_neg_deriv
    (f : ℝ → ℝ) (L d : ℝ) (hL : 0 < L)
    (hf : ContinuousOn f (Set.Icc 0 L)) (hf0 : f 0 = 1)
    (hd : HasDerivAt f d 0) (hdneg : d < 0)
    (hlt : ∀ x : ℝ, 0 < x → x ≤ L → f x < 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ x : ℝ, 0 ≤ x → x ≤ L → f x ≤ Real.exp (-c * x) := by
  obtain ⟨c, hc, hbound⟩ :=
    exists_pos_linear_upper_bound_of_neg_deriv f L d hL hf hf0 hd hdneg hlt
  refine ⟨c, hc, ?_⟩
  intro x hx hxL
  calc
    f x ≤ 1 - c * x := hbound x hx hxL
    _ = (-c * x) + 1 := by ring
    _ ≤ Real.exp (-c * x) := Real.add_one_le_exp (-c * x)

/-- The actual root curve has norm derivative `-Re κ` at zero. -/
theorem stableRootCurve_norm_hasDerivAt_zero (κ : ℂ) :
    HasDerivAt (fun θ : ℝ => ‖stableRootCurve κ θ‖) (-κ.re) 0 := by
  have hs : HasDerivAt (fun θ : ℝ => ‖stableRootCurve κ θ‖ ^ 2)
      (2 * (-κ.re)) 0 := by
    simpa only [stableRootCurve_zero, Complex.inner, map_one, mul_one, Complex.neg_re]
      using (stableRootCurve_hasDerivAt_zero κ).norm_sq
  have hnonzero : ‖stableRootCurve κ 0‖ ^ 2 ≠ 0 := by
    simp only [stableRootCurve_zero, norm_one, one_pow, ne_eq, one_ne_zero, not_false_eq_true]
  have hsqrt := hs.sqrt hnonzero
  simpa only [Real.sqrt_sq, norm_nonneg, stableRootCurve_zero, norm_one, one_pow,
    Real.sqrt_one, mul_one, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
    using hsqrt

/-- For each parameter in the open right half-plane, the actual root curve
obeys the exponential estimate on the entire closed interval `[0, π]`. -/
theorem stableRootCurve_exp_decay (κ : ℂ) (hκ : 0 < κ.re) :
    ∃ c : ℝ, 0 < c ∧ ∀ θ : ℝ, 0 ≤ θ → θ ≤ Real.pi →
      ‖stableRootCurve κ θ‖ ≤ Real.exp (-c * θ) := by
  apply exists_pos_exp_upper_bound_of_neg_deriv
    (fun θ : ℝ => ‖stableRootCurve κ θ‖) Real.pi (-κ.re) Real.pi_pos
  · exact (stableRootCurve_contDiff κ hκ).continuous.norm.continuousOn
  · simp only [stableRootCurve_zero, norm_one]
  · exact stableRootCurve_norm_hasDerivAt_zero κ
  · exact neg_neg_of_pos hκ
  · exact stableRootCurve_norm_lt_one κ hκ

#print axioms exists_pos_linear_upper_bound_of_neg_deriv
#print axioms exists_pos_exp_upper_bound_of_neg_deriv
#print axioms stableRootCurve_norm_hasDerivAt_zero
#print axioms stableRootCurve_exp_decay

end MF21Restart
