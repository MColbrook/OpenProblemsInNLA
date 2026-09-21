import MF21Restart.ActualSimpleRoots
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Exclusion of residual zeros below pi in the final phase window of
manuscript Lemma 4. The endpoint pi is deliberately excluded from the
nonvanishing conclusion. See `FINAL_PHASE_WINDOW_STATEMENTS.md`.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace MF21Restart

theorem manuscriptFinalPhaseWindow_eventually_in_upper_half
    (m : ℕ) (hm : 2 ≤ m) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ θ : ℝ, θ ∈ Set.Icc 0 Real.pi →
        |manuscriptPhaseFn m n θ - (n + 1 : ℝ) * Real.pi| ≤ Real.pi / 4 →
        Real.pi / 2 ≤ θ := by
  obtain ⟨B, hB, heta⟩ := manuscriptEta_bounded_with_derivative m (by omega)
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 ((2 * B + Real.pi) / Real.pi))
  have hN1 : 1 ≤ N := by
    have hN1r : (1 : ℝ) < N := (le_max_left _ _).trans_lt hN
    exact_mod_cast hN1r.le
  refine ⟨N, hN1, ?_⟩
  intro n hn θ hθ hcell
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hthreshold : 2 * B + Real.pi < (n : ℝ) * Real.pi :=
    (div_lt_iff₀ Real.pi_pos).mp (((le_max_right _ _).trans_lt hN).trans_le hNn)
  have hetalower := (abs_le.mp (heta θ hθ).1).1
  have hphase := (abs_le.mp hcell).1
  unfold manuscriptPhaseFn at hphase
  by_contra hnot
  have hθlt : θ < Real.pi / 2 := lt_of_not_ge hnot
  have hmul := mul_lt_mul_of_pos_left hθlt (show 0 < (n + 2 : ℝ) by positivity)
  nlinarith only [hmul, hphase, hetalower, hthreshold, Real.pi_pos]

private theorem final_window_exp_eventually_small
    (c C : ℝ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      C * Real.exp (-c * (n : ℝ) * Real.pi / 2) < 1 / Real.pi := by
  have hneg : -c * Real.pi / 2 < 0 :=
    div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hc) Real.pi_pos) (by norm_num)
  have hlin : Tendsto (fun n : ℕ => (-c * Real.pi / 2) * (n : ℝ)) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg hneg).mpr tendsto_natCast_atTop_atTop
  have harg (n : ℕ) : (-c * Real.pi / 2) * (n : ℝ) =
      -c * (n : ℝ) * Real.pi / 2 := by ring
  have hexp : Tendsto (fun n : ℕ => Real.exp (-c * (n : ℝ) * Real.pi / 2))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, harg] using Real.tendsto_exp_atBot.comp hlin
  have hscaled : Tendsto (fun n : ℕ => C * Real.exp (-c * (n : ℝ) * Real.pi / 2))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hexp.const_mul C
  exact Filter.eventually_atTop.mp
    ((tendsto_order.mp hscaled).2 (1 / Real.pi) (by positivity))

/-- The phase derivative estimate and Jordan's sine inequality produce the
factor pi-theta needed to compare with the actual endpoint error bound. -/
private theorem final_window_sine_lower_bound
    (m n : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi)
    (hcell : |manuscriptPhaseFn m n θ - (n + 1 : ℝ) * Real.pi| ≤ Real.pi / 4)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) Real.pi,
      (n + 2 : ℝ) / 2 ≤ deriv (manuscriptPhaseFn m n) t) :
    (n + 2 : ℝ) / Real.pi * (Real.pi - θ) ≤
      |Real.sin (manuscriptPhaseFn m n θ)| := by
  have hcont : ContinuousOn (manuscriptPhaseFn m n) (Set.Icc 0 Real.pi) :=
    fun t ht => (manuscriptPhaseFn_hasDerivAt m n hm t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (manuscriptPhaseFn m n)
      (interior (Set.Icc 0 Real.pi)) := by
    intro t ht
    exact (manuscriptPhaseFn_hasDerivAt m n hm t
      (Set.mem_of_mem_of_subset ht interior_subset)).differentiableAt.differentiableWithinAt
  have hgrowth := (convex_Icc (0 : ℝ) Real.pi).mul_sub_le_image_sub_of_le_deriv
    hcont hdiff (fun t ht => hderiv t (Set.mem_of_mem_of_subset ht interior_subset))
    θ hθ Real.pi ⟨Real.pi_pos.le, le_rfl⟩ hθ.2
  rw [manuscriptPhaseFn_pi m n hm] at hgrowth
  have hsine := Real.mul_abs_le_abs_sin
    (hcell.trans (by linarith [Real.pi_pos] : Real.pi / 4 ≤ Real.pi / 2))
  have hshift :
      |Real.sin (manuscriptPhaseFn m n θ - (n + 1 : ℝ) * Real.pi)| =
        |Real.sin (manuscriptPhaseFn m n θ)| := by
    simpa only [Nat.cast_add, Nat.cast_one, abs_mul, abs_pow, abs_neg, abs_one,
      one_pow, one_mul] using
      congrArg abs (Real.sin_sub_nat_mul_pi (manuscriptPhaseFn m n θ) (n + 1))
  rw [hshift] at hsine
  have hgap : (n + 1 : ℝ) * Real.pi - manuscriptPhaseFn m n θ ≤
      |manuscriptPhaseFn m n θ - (n + 1 : ℝ) * Real.pi| := by
    calc
      _ ≤ |(n + 1 : ℝ) * Real.pi - manuscriptPhaseFn m n θ| := le_abs_self _
      _ = _ := abs_sub_comm _ _
  calc
    (n + 2 : ℝ) / Real.pi * (Real.pi - θ) =
        (2 / Real.pi) * ((n + 2 : ℝ) / 2 * (Real.pi - θ)) := by ring
    _ ≤ (2 / Real.pi) * ((n + 1 : ℝ) * Real.pi - manuscriptPhaseFn m n θ) :=
      mul_le_mul_of_nonneg_left hgrowth (by positivity)
    _ ≤ (2 / Real.pi) * |manuscriptPhaseFn m n θ - (n + 1 : ℝ) * Real.pi| :=
      mul_le_mul_of_nonneg_left hgap (by positivity)
    _ ≤ |Real.sin (manuscriptPhaseFn m n θ)| := hsine

theorem manuscriptFinalPhaseWindow_eventual_nonzero (m : ℕ) (hm : 2 ≤ m) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ θ : ℝ, θ ∈ Set.Ioo 0 Real.pi →
        |manuscriptPhaseFn m n θ - (n + 1 : ℝ) * Real.pi| ≤ Real.pi / 4 →
        Real.pi / 2 ≤ θ ∧ manuscriptResidual m n hm θ ≠ 0 := by
  obtain ⟨Nhalf, hNhalf, hhalf⟩ := manuscriptFinalPhaseWindow_eventually_in_upper_half m hm
  obtain ⟨Nderiv, hderiv⟩ := manuscriptPhaseFn_eventual_derivative_bounds m (by omega)
  obtain ⟨c, C, hc, hC, herror⟩ := manuscriptError_endpoint_bound m hm
  obtain ⟨Nexp, hexp⟩ := final_window_exp_eventually_small c C hc
  refine ⟨max Nhalf (max Nderiv Nexp), hNhalf.trans (le_max_left _ _), ?_⟩
  intro n hn θ hθ hcell
  have hnHalf : Nhalf ≤ n := (le_max_left _ _).trans hn
  have hnDeriv : Nderiv ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hnExp : Nexp ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  have hθcc : θ ∈ Set.Icc 0 Real.pi := ⟨hθ.1.le, hθ.2.le⟩
  have hθhalf := hhalf n hnHalf θ hθcc hcell
  have hsin := final_window_sine_lower_bound m n (by omega) θ hθcc hcell
    (fun t ht => (hderiv n hnDeriv t ht).1)
  have hsmall := hexp n hnExp
  have hgap : 0 < Real.pi - θ := sub_pos.mpr hθ.2
  have hsize : 0 < (n + 1 : ℝ) * (Real.pi - θ) := mul_pos (by positivity) hgap
  have hEstrict : |manuscriptError m n hm θ| <
      (n + 2 : ℝ) / Real.pi * (Real.pi - θ) := by
    calc
      |manuscriptError m n hm θ| ≤
          C * (n + 1 : ℝ) * (Real.pi - θ) *
            Real.exp (-c * (n : ℝ) * Real.pi / 2) := herror n θ hθhalf hθ.2.le
      _ = (C * Real.exp (-c * (n : ℝ) * Real.pi / 2)) *
          ((n + 1 : ℝ) * (Real.pi - θ)) := by ring
      _ < (1 / Real.pi) * ((n + 1 : ℝ) * (Real.pi - θ)) :=
        mul_lt_mul_of_pos_right hsmall hsize
      _ = (n + 1 : ℝ) * ((1 / Real.pi) * (Real.pi - θ)) := by ring
      _ ≤ (n + 2 : ℝ) * ((1 / Real.pi) * (Real.pi - θ)) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (by positivity) hgap.le)
      _ = (n + 2 : ℝ) / Real.pi * (Real.pi - θ) := by ring
  refine ⟨hθhalf, ?_⟩
  intro hzero
  have hsinlt := hEstrict.trans_le hsin
  have heq : Real.sin (manuscriptPhaseFn m n θ) = -manuscriptError m n hm θ := by
    unfold manuscriptResidual at hzero
    linarith only [hzero]
  rw [heq, abs_neg] at hsinlt
  exact (lt_irrefl _) hsinlt

#print axioms manuscriptFinalPhaseWindow_eventually_in_upper_half
#print axioms manuscriptFinalPhaseWindow_eventual_nonzero

end MF21Restart
