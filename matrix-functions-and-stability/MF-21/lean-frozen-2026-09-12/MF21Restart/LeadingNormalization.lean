import MF21Restart.LeadingBoundaryCoefficients
import MF21Restart.BoundaryNormalizer
import MF21Restart.NormalizedErrorCoefficient
import MF21Restart.PhaseMonotonicity

/-! Exact leading normalization in (16) and the coefficient quotient in (18).
Statements were fixed in LEADING_NORMALIZATION_STATEMENTS.md before this file.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

theorem boundaryPhaseMultiplier_factor (m : ℕ) (θ : ℝ) :
    boundaryPhaseMultiplier m θ = oscillatoryRoot θ ^ (m - 1) *
      Complex.exp (((2 * manuscriptPsi m θ : ℝ) : ℂ) * Complex.I) := by
  unfold boundaryPhaseMultiplier oscillatoryRoot
  have he : (((((m - 1 : ℕ) : ℝ) * θ + 2 * manuscriptPsi m θ : ℝ) : ℂ) * Complex.I) =
      (m - 1 : ℕ) * ((θ : ℂ) * Complex.I) +
        ((2 * manuscriptPsi m θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [he, Complex.exp_add, Complex.exp_nat_mul]

private theorem phaseProduct_conj_sq_phase (m : ℕ) (hm : 2 ≤ m)
    (θ : ℝ) (hθ : 0 < θ) (hθπ : θ ≤ Real.pi) :
    ((starRingEnd ℂ) (manuscriptPhaseProduct m θ)) ^ 2 *
        Complex.exp (((2 * manuscriptPsi m θ : ℝ) : ℂ) * Complex.I) =
      (Complex.normSq (manuscriptPhaseProduct m θ) : ℂ) := by
  have hf := manuscriptPhaseProduct_ne_zero m (by omega) θ hθ hθπ
  have hc : (starRingEnd ℂ) (manuscriptPhaseProduct m θ) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).mpr hf
  rw [← manuscriptPhaseProduct_div_conj m (by omega) θ hθ hθπ,
    Complex.normSq_eq_conj_mul_self]
  field_simp [hc]
  <;> ring

theorem manuscriptNormalizer_eq_leading (m n : ℕ) (hm : 2 ≤ m)
    (θ : ℝ) (hθ : 0 < θ) (hθπ : θ ≤ Real.pi) :
    manuscriptNormalizer m n θ =
      boundaryCoefficient m (characteristicRoots m θ)
          (boundaryLeadingZIndices m (by omega)) *
        (2 * Complex.I * boundaryPhaseMultiplier m θ) *
        boundaryExteriorProduct m θ ^ (n + m) := by
  have hz : (oscillatoryRoot θ)⁻¹ ^ (m - 1) * oscillatoryRoot θ ^ (m - 1) = 1 := by
    rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ (oscillatoryRoot_ne_zero θ))]
  symm
  calc
    _ = (-2 * Complex.I) *
        ((Matrix.vandermonde (stableRootList m θ)).det *
          (Matrix.vandermonde (exteriorRootList m θ)).det) *
        boundaryExteriorProduct m θ ^ (n + m + 1) *
        (((starRingEnd ℂ) (manuscriptPhaseProduct m θ)) ^ 2 *
          Complex.exp (((2 * manuscriptPsi m θ : ℝ) : ℂ) * Complex.I)) *
        ((oscillatoryRoot θ)⁻¹ ^ (m - 1) * oscillatoryRoot θ ^ (m - 1)) := by
      rw [boundaryCoefficient_leadingZ m hm, boundaryPhaseMultiplier_factor, pow_succ]
      ring
    _ = manuscriptNormalizer m n θ := by
      rw [phaseProduct_conj_sq_phase m hm θ hθ hθπ, hz, mul_one]
      rfl

theorem boundaryCoefficient_leading_phase_relation (m : ℕ) (hm : 2 ≤ m)
    (θ : ℝ) (hθ : 0 < θ) (hθπ : θ ≤ Real.pi) :
    boundaryCoefficient m (characteristicRoots m θ)
        (boundaryLeadingZInvIndices m (by omega)) =
      -boundaryCoefficient m (characteristicRoots m θ)
        (boundaryLeadingZIndices m (by omega)) * boundaryPhaseMultiplier m θ ^ 2 := by
  have hf := manuscriptPhaseProduct_ne_zero m (by omega) θ hθ hθπ
  have hc : (starRingEnd ℂ) (manuscriptPhaseProduct m θ) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).mpr hf
  have hz := pow_ne_zero (m - 1) (oscillatoryRoot_ne_zero θ)
  rw [boundaryCoefficient_leadingZ m hm, boundaryCoefficient_leadingZInv m hm,
    boundaryPhaseMultiplier_factor,
    ← manuscriptPhaseProduct_div_conj m (by omega) θ hθ hθπ]
  simp only [inv_pow]
  field_simp [hc, hz]
  <;> ring

theorem leading_phase_quotient (m n : ℕ) (hm : 1 ≤ m) (θ : ℝ) :
    oscillatoryRoot θ ^ (n + m) / boundaryPhaseMultiplier m θ =
      Complex.exp ((manuscriptPhaseFn m n θ : ℂ) * Complex.I) := by
  unfold oscillatoryRoot boundaryPhaseMultiplier
  rw [← Complex.exp_nat_mul, ← Complex.exp_sub]
  congr 1
  simp only [manuscriptPhaseFn, manuscriptEta, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_ofNat, Nat.cast_add,
    Nat.cast_sub hm, Nat.cast_one, Complex.ofReal_one]
  ring

theorem boundaryLeadingTerms_eq_normalizer_mul_sin (m n : ℕ) (hm : 2 ≤ m)
    (θ : ℝ) (hθ : 0 < θ) (hθπ : θ ≤ Real.pi) :
    boundaryCoefficient m (characteristicRoots m θ)
        (boundaryLeadingZIndices m (by omega)) *
        (∏ i ∈ boundaryLeadingZIndices m (by omega), characteristicRoots m θ i) ^ (n + m) +
      boundaryCoefficient m (characteristicRoots m θ)
        (boundaryLeadingZInvIndices m (by omega)) *
        (∏ i ∈ boundaryLeadingZInvIndices m (by omega), characteristicRoots m θ i) ^ (n + m) =
      manuscriptNormalizer m n θ * (Real.sin (manuscriptPhaseFn m n θ) : ℂ) := by
  have hz := pow_ne_zero (n + m) (oscillatoryRoot_ne_zero θ)
  have hU := boundaryPhaseMultiplier_ne_zero m θ
  have hs : oscillatoryRoot θ ^ (n + m) / boundaryPhaseMultiplier m θ -
      boundaryPhaseMultiplier m θ / oscillatoryRoot θ ^ (n + m) =
      2 * Complex.I * (Real.sin (manuscriptPhaseFn m n θ) : ℂ) := by
    have hi : boundaryPhaseMultiplier m θ / oscillatoryRoot θ ^ (n + m) =
        Complex.exp (-((manuscriptPhaseFn m n θ : ℝ) : ℂ) * Complex.I) := by
      rw [← inv_div, leading_phase_quotient m n (by omega), ← Complex.exp_neg]
      congr 1
      ring
    rw [leading_phase_quotient m n (by omega), hi]
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  rw [boundaryLeadingZIndices_rootProduct m hm,
    boundaryLeadingZInvIndices_rootProduct m hm,
    boundaryCoefficient_leading_phase_relation m hm θ hθ hθπ,
    manuscriptNormalizer_eq_leading m n hm θ hθ hθπ,
    mul_pow, mul_pow, inv_pow]
  have hs' : oscillatoryRoot θ ^ (n + m) -
      boundaryPhaseMultiplier m θ ^ 2 * (oscillatoryRoot θ ^ (n + m))⁻¹ =
      (2 * Complex.I * boundaryPhaseMultiplier m θ) *
        (Real.sin (manuscriptPhaseFn m n θ) : ℂ) := by
    calc
      _ = boundaryPhaseMultiplier m θ *
          (oscillatoryRoot θ ^ (n + m) / boundaryPhaseMultiplier m θ -
            boundaryPhaseMultiplier m θ / oscillatoryRoot θ ^ (n + m)) := by
        field_simp [hU, hz]
        <;> ring
      _ = _ := by rw [hs]; ring
  calc
    _ = boundaryCoefficient m (characteristicRoots m θ)
        (boundaryLeadingZIndices m (by omega)) * boundaryExteriorProduct m θ ^ (n + m) *
        (oscillatoryRoot θ ^ (n + m) -
          boundaryPhaseMultiplier m θ ^ 2 * (oscillatoryRoot θ ^ (n + m))⁻¹) := by ring
    _ = _ := by rw [hs']; ring

theorem normalizedErrorTerm_eq_raw_quotient (m n : ℕ) (hm : 2 ≤ m)
    (s : Finset (Fin (2 * m))) (hs : s.card = m)
    (θ : ℝ) (hθ : 0 < θ) (hθπ : θ ≤ Real.pi) :
    normalizedErrorCoefficient m (by omega) s hs θ *
        boundaryProductRatio m θ s ^ (n + m) =
      boundaryCoefficient m (characteristicRoots m θ) s *
        (∏ i ∈ s, characteristicRoots m θ i) ^ (n + m) /
          manuscriptNormalizer m n θ := by
  have hm1 : 1 ≤ m := by omega
  have hN := manuscriptNormalizer_ne_zero m n hm θ hθ hθπ
  rw [manuscriptNormalizer_eq_leading m n hm θ hθ hθπ] at hN
  have hA : boundaryCoefficient m (characteristicRoots m θ)
      (boundaryLeadingZIndices m hm1) ≠ 0 := (mul_ne_zero_iff.mp
        (mul_ne_zero_iff.mp hN).1).1
  have hU := boundaryPhaseMultiplier_ne_zero m θ
  have hQ := pow_ne_zero (n + m) (boundaryExteriorProduct_ne_zero m θ)
  rw [normalizedErrorCoefficient,
    ← boundaryCoefficient_ratio_eq_normalized m s _ hs
      (card_boundaryLeadingZIndices m hm1) θ (ne_of_gt hθ),
    boundaryProductRatio, div_pow,
    manuscriptNormalizer_eq_leading m n hm θ hθ hθπ]
  field_simp [hA, hU, hQ, Complex.I_ne_zero]
  <;> ring

#print axioms boundaryPhaseMultiplier_factor
#print axioms manuscriptNormalizer_eq_leading
#print axioms boundaryCoefficient_leading_phase_relation
#print axioms leading_phase_quotient
#print axioms boundaryLeadingTerms_eq_normalizer_mul_sin
#print axioms normalizedErrorTerm_eq_raw_quotient

end MF21Restart
