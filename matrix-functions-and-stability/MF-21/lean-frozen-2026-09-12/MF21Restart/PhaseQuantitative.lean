import MF21Restart.PhaseWindowIndexing
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Quantitative manuscript Lemma 4 for the actual original-index eigenangle
and the exact phase preimage. Identification of that preimage with the
separately constructed implicit function Y is not assumed here.
The prior lock is `PHASE_QUANTITATIVE_STATEMENTS.md`.
-/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

private theorem phase_grid_preimage_exists
    (m n j : ℕ) (hm : 1 ≤ m) (hj : 1 ≤ j) (hjn : j ≤ n) :
    ∃ y : ℝ, y ∈ Set.Ioo 0 Real.pi ∧
      manuscriptPhaseFn m n y = (j : ℝ) * Real.pi := by
  have hcont : ContinuousOn (manuscriptPhaseFn m n) (Set.Icc 0 Real.pi) :=
    fun t ht => (manuscriptPhaseFn_hasDerivAt m n hm t ht).continuousAt.continuousWithinAt
  have hleft : manuscriptPhaseFn m n 0 < (j : ℝ) * Real.pi := by
    rw [manuscriptPhaseFn_zero m n hm]
    have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hjreal : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hmprod : 0 ≤ ((m : ℝ) - 1) * Real.pi / 2 :=
      div_nonneg (mul_nonneg (sub_nonneg.mpr hmreal) Real.pi_pos.le) (by norm_num)
    have hjprod : 0 < (j : ℝ) * Real.pi :=
      mul_pos (lt_of_lt_of_le zero_lt_one hjreal) Real.pi_pos
    linarith only [hmprod, hjprod]
  have hright : (j : ℝ) * Real.pi < manuscriptPhaseFn m n Real.pi := by
    rw [manuscriptPhaseFn_pi m n hm]
    have hjnr : (j : ℝ) ≤ n := by exact_mod_cast hjn
    have hmul := mul_le_mul_of_nonneg_right hjnr Real.pi_pos.le
    nlinarith only [hmul, Real.pi_pos]
  obtain ⟨y, hy, hyF⟩ := intermediate_value_Icc Real.pi_pos.le hcont
    (show (j : ℝ) * Real.pi ∈ Set.Icc
      (manuscriptPhaseFn m n 0) (manuscriptPhaseFn m n Real.pi) from
      ⟨hleft.le, hright.le⟩)
  refine ⟨y, ⟨?_, ?_⟩, hyF⟩
  · by_contra hnot
    have heq : y = 0 := le_antisymm (le_of_not_gt hnot) hy.1
    exact hleft.ne (by simpa only [heq] using hyF)
  · by_contra hnot
    have heq : y = Real.pi := le_antisymm hy.2 (le_of_not_gt hnot)
    exact hright.ne (by simpa only [heq] using hyF.symm)

private theorem phase_separation_lower_bound
    (m n : ℕ) (hm : 1 ≤ m) (x y : ℝ)
    (hx : x ∈ Set.Icc 0 Real.pi) (hy : y ∈ Set.Icc 0 Real.pi)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) Real.pi,
      (n + 2 : ℝ) / 2 ≤ deriv (manuscriptPhaseFn m n) t) :
    (n + 2 : ℝ) / 2 * |x - y| ≤
      |manuscriptPhaseFn m n x - manuscriptPhaseFn m n y| := by
  have hcont : ContinuousOn (manuscriptPhaseFn m n) (Set.Icc 0 Real.pi) :=
    fun t ht => (manuscriptPhaseFn_hasDerivAt m n hm t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (manuscriptPhaseFn m n)
      (interior (Set.Icc 0 Real.pi)) := by
    intro t ht
    exact (manuscriptPhaseFn_hasDerivAt m n hm t
      (Set.mem_of_mem_of_subset ht interior_subset)).differentiableAt.differentiableWithinAt
  have hgrowth := (convex_Icc (0 : ℝ) Real.pi).mul_sub_le_image_sub_of_le_deriv
    hcont hdiff (fun t ht => hderiv t (Set.mem_of_mem_of_subset ht interior_subset))
  rcases le_total y x with hyx | hxy
  · rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact (hgrowth y hy x hx hyx).trans (le_abs_self _)
  · rw [abs_sub_comm x y, abs_of_nonneg (sub_nonneg.mpr hxy),
      abs_sub_comm (manuscriptPhaseFn m n x) (manuscriptPhaseFn m n y)]
    exact (hgrowth x hx y hy hxy).trans (le_abs_self _)

private theorem phase_discrepancy_le_error
    (m n j : ℕ) (hm : 2 ≤ m) (θ : ℝ)
    (hcell : |manuscriptPhaseFn m n θ - (j : ℝ) * Real.pi| ≤ Real.pi / 4)
    (hzero : manuscriptResidual m n hm θ = 0) :
    2 * |manuscriptPhaseFn m n θ - (j : ℝ) * Real.pi| ≤
      Real.pi * |manuscriptError m n hm θ| := by
  have hsine := Real.mul_abs_le_abs_sin
    (hcell.trans (by linarith [Real.pi_pos] : Real.pi / 4 ≤ Real.pi / 2))
  rw [Real.sin_sub_nat_mul_pi, abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, one_mul] at hsine
  have heq : Real.sin (manuscriptPhaseFn m n θ) = -manuscriptError m n hm θ := by
    change Real.sin (manuscriptPhaseFn m n θ) + manuscriptError m n hm θ = 0 at hzero
    linarith only [hzero]
  rw [heq, abs_neg] at hsine
  calc
    2 * |manuscriptPhaseFn m n θ - (j : ℝ) * Real.pi| =
        Real.pi * ((2 / Real.pi) *
          |manuscriptPhaseFn m n θ - (j : ℝ) * Real.pi|) := by
            field_simp [Real.pi_ne_zero] <;> ring
    _ ≤ Real.pi * |manuscriptError m n hm θ| :=
      mul_le_mul_of_nonneg_left hsine Real.pi_pos.le

/-- Actual indexed eigenangles satisfy the quantitative bounds of
manuscript (19), with y characterized by its exact phase equation. -/
theorem eigenvalue_eventual_quantitative_phase_preimage (m : ℕ) (hm : 2 ≤ m) :
    ∃ (N J : ℕ) (C c : ℝ),
      1 ≤ N ∧ 1 ≤ J ∧ 0 < C ∧ 0 < c ∧
      ∀ n : ℕ, N ≤ n → ∀ j : ℕ, J ≤ j → j ≤ n →
        ∃ θ y : ℝ,
          θ ∈ Set.Ioo 0 Real.pi ∧ y ∈ Set.Ioo 0 Real.pi ∧
          symbol m θ = eigenvalue m n j ∧
          manuscriptPhaseFn m n y = (j : ℝ) * Real.pi ∧
          |θ - y| ≤ C * Real.exp (-c * (j : ℝ)) / (n + 2 : ℝ) ∧
          θ ≤ C * (j : ℝ) / (n + 2 : ℝ) ∧
          y ≤ C * (j : ℝ) / (n + 2 : ℝ) := by
  obtain ⟨Ni, J, hNi, hJ, hindexed⟩ := eigenvalue_eventual_phase_window m hm
  obtain ⟨Nd, hderiv⟩ := manuscriptPhaseFn_eventual_derivative_bounds m (by omega)
  obtain ⟨c₀, C₀, hc₀, hC₀, herror⟩ := manuscriptError_exp_bounds m hm
  obtain ⟨B, hB, heta⟩ := manuscriptEta_bounded_with_derivative m (by omega)
  let K : ℝ := B + 9 * Real.pi / 4
  let D : ℝ := C₀ * Real.exp (c₀ * K)
  let c : ℝ := c₀ * Real.pi
  let S : ℝ := Real.pi + Real.pi / 4 + B
  let C : ℝ := max (Real.pi * D) S
  have hD : 0 < D := mul_pos hC₀ (Real.exp_pos _)
  have hc : 0 < c := mul_pos hc₀ Real.pi_pos
  have hCphase : Real.pi * D ≤ C := le_max_left _ _
  have hCsize : S ≤ C := le_max_right _ _
  have hC : 0 < C := (mul_pos Real.pi_pos hD).trans_le hCphase
  refine ⟨max Ni Nd, J, C, c, hNi.trans (le_max_left _ _), hJ, hC, hc, ?_⟩
  intro n hn j hJj hjn
  have hnI : Ni ≤ n := (le_max_left _ _).trans hn
  have hnD : Nd ≤ n := (le_max_right _ _).trans hn
  have hj1 : 1 ≤ j := hJ.trans hJj
  have hjreal : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hjnonneg : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hnpositive : 0 < (n + 2 : ℝ) := by positivity
  obtain ⟨θ, hθ, hθvalue, hcell, hzero, _hsimple⟩ := hindexed n hnI j hJj hjn
  obtain ⟨y, hy, hyPhase⟩ := phase_grid_preimage_exists m n j (by omega) hj1 hjn
  have hθcc : θ ∈ Set.Icc 0 Real.pi := ⟨hθ.1.le, hθ.2.le⟩
  have hycc : y ∈ Set.Icc 0 Real.pi := ⟨hy.1.le, hy.2.le⟩
  have hnt : (j : ℝ) * Real.pi - K ≤ (n : ℝ) * θ := by
    have hphase := (abs_le.mp hcell).1
    have hlower := (abs_le.mp (heta θ hθcc).1).1
    unfold manuscriptPhaseFn at hphase
    dsimp only [K]
    nlinarith only [hphase, hlower, hθ.2.le]
  have harg : -c₀ * (n : ℝ) * θ ≤ c₀ * K + -c * (j : ℝ) := by
    have hmul := mul_le_mul_of_nonpos_left hnt (neg_nonpos.mpr hc₀.le)
    dsimp only [c]
    nlinarith only [hmul]
  have hE : |manuscriptError m n hm θ| ≤ D * Real.exp (-c * (j : ℝ)) := by
    calc
      |manuscriptError m n hm θ| ≤ C₀ * Real.exp (-c₀ * (n : ℝ) * θ) :=
        (herror n θ hθ.1.le hθ.2.le).1
      _ ≤ C₀ * Real.exp (c₀ * K + -c * (j : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) hC₀.le
      _ = D * Real.exp (-c * (j : ℝ)) := by rw [Real.exp_add]; dsimp only [D]; ring
  have hphaseBound : 2 * |manuscriptPhaseFn m n θ - (j : ℝ) * Real.pi| ≤
      (Real.pi * D) * Real.exp (-c * (j : ℝ)) := by
    calc
      2 * |manuscriptPhaseFn m n θ - (j : ℝ) * Real.pi| ≤
          Real.pi * |manuscriptError m n hm θ| :=
        phase_discrepancy_le_error m n j hm θ hcell hzero
      _ ≤ Real.pi * (D * Real.exp (-c * (j : ℝ))) :=
        mul_le_mul_of_nonneg_left hE Real.pi_pos.le
      _ = (Real.pi * D) * Real.exp (-c * (j : ℝ)) := by ring
  have hseparation := phase_separation_lower_bound m n (by omega) θ y hθcc hycc
    (fun t ht => (hderiv n hnD t ht).1)
  rw [hyPhase] at hseparation
  have hdist : |θ - y| ≤ C * Real.exp (-c * (j : ℝ)) / (n + 2 : ℝ) := by
    apply (le_div_iff₀ hnpositive).mpr
    have hnum : |θ - y| * (n + 2 : ℝ) ≤
        (Real.pi * D) * Real.exp (-c * (j : ℝ)) := by
      nlinarith only [hseparation, hphaseBound]
    exact hnum.trans (mul_le_mul_of_nonneg_right hCphase (Real.exp_pos _).le)
  have hshift : 0 ≤ Real.pi / 4 + B := by positivity
  have hshiftj := mul_le_mul_of_nonneg_left hjreal hshift
  have hθnum : (n + 2 : ℝ) * θ ≤ (j : ℝ) * Real.pi + Real.pi / 4 + B := by
    have hphase := (abs_le.mp hcell).2
    have hetaUpper := (abs_le.mp (heta θ hθcc).1).2
    unfold manuscriptPhaseFn at hphase
    linarith only [hphase, hetaUpper]
  have hynum : (n + 2 : ℝ) * y ≤ (j : ℝ) * Real.pi + B := by
    have hphase := hyPhase
    have hetaUpper := (abs_le.mp (heta y hycc).1).2
    unfold manuscriptPhaseFn at hphase
    linarith only [hphase, hetaUpper]
  have hθsize : θ ≤ C * (j : ℝ) / (n + 2 : ℝ) := by
    apply (le_div_iff₀ hnpositive).mpr
    calc
      θ * (n + 2 : ℝ) ≤ S * (j : ℝ) := by
        dsimp only [S]
        nlinarith only [hθnum, hshiftj]
      _ ≤ C * (j : ℝ) := mul_le_mul_of_nonneg_right hCsize hjnonneg
  have hysize : y ≤ C * (j : ℝ) / (n + 2 : ℝ) := by
    apply (le_div_iff₀ hnpositive).mpr
    calc
      y * (n + 2 : ℝ) ≤ S * (j : ℝ) := by
        dsimp only [S]
        nlinarith only [hynum, hshiftj, Real.pi_pos]
      _ ≤ C * (j : ℝ) := mul_le_mul_of_nonneg_right hCsize hjnonneg
  exact ⟨θ, y, hθ, hy, hθvalue, hyPhase, hdist, hθsize, hysize⟩

#print axioms eigenvalue_eventual_quantitative_phase_preimage

end MF21Restart
