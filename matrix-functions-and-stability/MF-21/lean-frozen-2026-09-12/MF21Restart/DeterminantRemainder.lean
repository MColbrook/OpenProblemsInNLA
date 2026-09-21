import MF21Restart.LeadingNormalization
import MF21Restart.BoundaryErrorBounds
import Mathlib.Analysis.Calculus.MeanValue

/-! The exact real determinant remainder of manuscript Lemma 3.
See DETERMINANT_REMAINDER_STATEMENTS.md for the prior statement lock. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

theorem boundaryLeadingSubsets_ne (m : ℕ) (hm : 2 ≤ m) :
    boundaryLeadingZIndices m (by omega) ≠ boundaryLeadingZInvIndices m (by omega) := by
  intro heq
  let i : Fin (2 * m) := ⟨m - 1, by omega⟩
  have hi : i ∈ boundaryLeadingZIndices m (by omega) := Finset.mem_insert_self _ _
  rw [heq] at hi
  simp only [boundaryLeadingZInvIndices, Finset.mem_insert, mem_boundaryExteriorIndices] at hi
  rcases hi with hi | hi
  · have hv := congrArg Fin.val hi
    dsimp [i] at hv
    omega
  · dsimp [i] at hi
    omega

private theorem sum_card_subsets_split (m : ℕ) (hm : 2 ≤ m)
    (f : Finset (Fin (2 * m)) → ℂ) :
    (∑ s ∈ (Finset.univ : Finset (Fin (2 * m))).powersetCard m, f s) =
      f (boundaryLeadingZIndices m (by omega)) +
        f (boundaryLeadingZInvIndices m (by omega)) +
          ∑ s : BoundaryNonleadingSubset m hm, f s.val := by
  classical
  let P := (Finset.univ : Finset (Fin (2 * m))).powersetCard m
  let a := boundaryLeadingZIndices m (by omega)
  let b := boundaryLeadingZInvIndices m (by omega)
  have ha : a ∈ P := by
    simp only [P, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    exact card_boundaryLeadingZIndices m (by omega)
  have hb : b ∈ P := by
    simp only [P, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    exact card_boundaryLeadingZInvIndices m (by omega)
  have hab : a ≠ b := boundaryLeadingSubsets_ne m hm
  have hbe : b ∈ P.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
  have hrest : (∑ s ∈ (P.erase a).erase b, f s) =
      ∑ s : BoundaryNonleadingSubset m hm, f s.val := by
    apply Finset.sum_subtype
    intro s
    simp only [Finset.mem_erase, P, Finset.mem_powersetCard, Finset.subset_univ,
      true_and, BoundaryNonleadingSubset]
    tauto
  change (∑ s ∈ P, f s) = _
  rw [← Finset.add_sum_erase P f ha, ← Finset.add_sum_erase (P.erase a) f hbe, hrest]
  exact (add_assoc _ _ _).symm

theorem manuscriptNormalizedDeterminant_eq_sin_add_error (m n : ℕ) (hm : 2 ≤ m)
    (θ : ℝ) (hθ : 0 < θ) (hθπ : θ ≤ Real.pi) :
    manuscriptNormalizedDeterminant m n θ =
      (Real.sin (manuscriptPhaseFn m n θ) : ℂ) + boundaryErrorExpression m n hm θ := by
  classical
  have hN := manuscriptNormalizer_ne_zero m n hm θ hθ hθπ
  unfold manuscriptNormalizedDeterminant manuscriptBoundaryDeterminant
  rw [boundaryDeterminant_card_grouped_expansion,
    sum_card_subsets_split m hm,
    boundaryLeadingTerms_eq_normalizer_mul_sin m n hm θ hθ hθπ,
    add_div]
  have hlead : manuscriptNormalizer m n θ *
      (Real.sin (manuscriptPhaseFn m n θ) : ℂ) / manuscriptNormalizer m n θ =
      (Real.sin (manuscriptPhaseFn m n θ) : ℂ) := by field_simp
  rw [hlead, Finset.sum_div]
  congr 1
  unfold boundaryErrorExpression
  apply Finset.sum_congr rfl
  intro s _
  exact (normalizedErrorTerm_eq_raw_quotient m n hm s.val s.property.1 θ hθ hθπ).symm

theorem boundaryErrorExpression_real (m n : ℕ) (hm : 2 ≤ m)
    (θ : ℝ) (hθ : 0 < θ) (hθπ : θ ≤ Real.pi) :
    ((boundaryErrorExpression m n hm θ).re : ℂ) = boundaryErrorExpression m n hm θ := by
  have h := manuscriptNormalizedDeterminant_real m n hm θ
  rw [manuscriptNormalizedDeterminant_eq_sin_add_error m n hm θ hθ hθπ,
    Complex.add_re, Complex.ofReal_re, Complex.ofReal_add] at h
  exact add_left_cancel h

def manuscriptError (m n : ℕ) (hm : 2 ≤ m) (θ : ℝ) : ℝ :=
  (boundaryErrorExpression m n hm θ).re

theorem manuscriptError_contDiffAt (m n : ℕ) (hm : 2 ≤ m)
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi) :
    ContDiffAt ℝ ⊤ (manuscriptError m n hm) θ := by
  convert! Complex.reCLM.contDiff.contDiffAt.comp θ
    (boundaryErrorExpression_contDiffAt m n hm θ hθ) using 1

theorem manuscriptError_deriv (m n : ℕ) (hm : 2 ≤ m)
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi) :
    deriv (manuscriptError m n hm) θ =
      (deriv (boundaryErrorExpression m n hm) θ).re := by
  have he := (boundaryErrorExpression_contDiffAt m n hm θ hθ).differentiableAt
    (by simp)
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ he.hasDerivAt
  exact h.deriv

theorem eigenvalue_iff_sin_add_manuscriptError_zero (m n : ℕ) (hm : 2 ≤ m)
    (θ : ℝ) (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    (∃ j : ℕ, 1 ≤ j ∧ j ≤ n ∧ eigenvalue m n j = symbol m θ) ↔
      Real.sin (manuscriptPhaseFn m n θ) + manuscriptError m n hm θ = 0 := by
  rw [eigenvalue_iff_manuscriptNormalizedDeterminant_zero m n hm θ hθ hθπ,
    manuscriptNormalizedDeterminant_eq_sin_add_error m n hm θ hθ hθπ.le,
    ← boundaryErrorExpression_real m n hm θ hθ hθπ.le,
    ← Complex.ofReal_add, Complex.ofReal_eq_zero]
  rfl

theorem manuscriptError_exp_bounds (m : ℕ) (hm : 2 ≤ m) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ n : ℕ, ∀ θ : ℝ, 0 ≤ θ → θ ≤ Real.pi →
        |manuscriptError m n hm θ| ≤ C * Real.exp (-c * (n : ℝ) * θ) ∧
        |deriv (manuscriptError m n hm) θ| ≤
          C * (n + 1 : ℝ) * Real.exp (-c * (n : ℝ) * θ) := by
  obtain ⟨c, C, hc, hC, hbound⟩ := boundaryErrorExpression_exp_bounds m hm
  refine ⟨c, C, hc, hC, ?_⟩
  intro n θ hθ hθπ
  have hb := hbound n θ hθ hθπ
  constructor
  · exact (Complex.abs_re_le_norm _).trans hb.1
  · rw [manuscriptError_deriv m n hm θ ⟨hθ, hθπ⟩]
    exact (Complex.abs_re_le_norm _).trans hb.2

theorem manuscriptError_pi (m n : ℕ) (hm : 2 ≤ m) :
    manuscriptError m n hm Real.pi = 0 := by
  have h := manuscriptNormalizedDeterminant_eq_sin_add_error m n hm Real.pi
    Real.pi_pos le_rfl
  have hs : Real.sin (manuscriptPhaseFn m n Real.pi) = 0 := by
    rw [manuscriptPhaseFn_pi m n (by omega)]
    simpa only [Nat.cast_add, Nat.cast_one] using Real.sin_nat_mul_pi (n + 1)
  rw [manuscriptNormalizedDeterminant, manuscriptBoundaryDeterminant_pi m n hm,
    zero_div, hs, Complex.ofReal_zero, zero_add] at h
  unfold manuscriptError
  rw [← h, Complex.zero_re]

theorem manuscriptError_endpoint_bound (m : ℕ) (hm : 2 ≤ m) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ n : ℕ, ∀ θ : ℝ, Real.pi / 2 ≤ θ → θ ≤ Real.pi →
        |manuscriptError m n hm θ| ≤
          C * (n + 1 : ℝ) * (Real.pi - θ) * Real.exp (-c * (n : ℝ) * Real.pi / 2) := by
  obtain ⟨c, C, hc, hC, hbound⟩ := manuscriptError_exp_bounds m hm
  refine ⟨c, C, hc, hC, ?_⟩
  intro n θ hθ hθπ
  have hθ0 : 0 ≤ θ := (half_pos Real.pi_pos).le.trans hθ
  have hd : ∀ t ∈ Set.Icc θ Real.pi, DifferentiableAt ℝ (manuscriptError m n hm) t := by
    intro t ht
    exact (manuscriptError_contDiffAt m n hm t ⟨hθ0.trans ht.1, ht.2⟩).differentiableAt
      (by simp)
  have hb : ∀ t ∈ Set.Icc θ Real.pi,
      ‖deriv (manuscriptError m n hm) t‖ ≤
        C * (n + 1 : ℝ) * Real.exp (-c * (n : ℝ) * Real.pi / 2) := by
    intro t ht
    have ht0 := hθ0.trans ht.1
    have he : Real.exp (-c * (n : ℝ) * t) ≤ Real.exp (-c * (n : ℝ) * Real.pi / 2) := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonpos_left (hθ.trans ht.1)
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (Nat.cast_nonneg n))
      nlinarith only [hmul]
    have hv : ‖deriv (manuscriptError m n hm) t‖ ≤
        C * (n + 1 : ℝ) * Real.exp (-c * (n : ℝ) * t) := by
      simpa only [Real.norm_eq_abs] using (hbound n t ht0 ht.2).2
    exact hv.trans (mul_le_mul_of_nonneg_left he (by positivity))
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_Icc θ Real.pi)
    (Set.left_mem_Icc.mpr hθπ) (Set.right_mem_Icc.mpr hθπ)
  rw [manuscriptError_pi, zero_sub, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hθπ)] at hmv
  calc
    _ ≤ (C * (n + 1 : ℝ) * Real.exp (-c * (n : ℝ) * Real.pi / 2)) * (Real.pi - θ) := hmv
    _ = _ := by ring

#print axioms boundaryLeadingSubsets_ne
#print axioms manuscriptNormalizedDeterminant_eq_sin_add_error
#print axioms boundaryErrorExpression_real
#print axioms manuscriptError_contDiffAt
#print axioms manuscriptError_deriv
#print axioms eigenvalue_iff_sin_add_manuscriptError_zero
#print axioms manuscriptError_exp_bounds
#print axioms manuscriptError_pi
#print axioms manuscriptError_endpoint_bound

end MF21Restart
