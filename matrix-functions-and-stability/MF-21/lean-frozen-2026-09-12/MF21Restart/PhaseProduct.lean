import MF21Restart.PhaseZero
import MF21Restart.CharacteristicRoots

/-!
The actual phase product preceding manuscript equation (15). Its polar
representation uses the sum of the individual real arguments, without
replacing that sum by the principal argument of the product. The scalar
factor in the actual product is positive on 0 < theta <= pi, preserving
the positive phase sign. PHASE_PRODUCT_STATEMENTS.md precedes this proof.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

def manuscriptPhaseProduct (m : ℕ) (theta : ℝ) : ℂ :=
  ∏ ell : Fin (m - 1),
    (1 - stableRootCurve (rootKappa m (ell.val + 1)) theta *
      (oscillatoryRoot theta)⁻¹)

def normalizedPhaseProduct (m : ℕ) (theta : ℝ) : ℂ :=
  ∏ ell : Fin (m - 1), phaseNormalized (rootKappa m (ell.val + 1)) theta

theorem normalizedPhaseProduct_contDiff (m : ℕ) (hm : 1 ≤ m) :
    ContDiff ℝ ⊤ (normalizedPhaseProduct m) := by
  unfold normalizedPhaseProduct
  apply contDiff_prod
  intro ell _
  exact phaseNormalized_contDiff _
    (rootKappa_re_pos m (ell.val + 1) (by omega) (by have := ell.isLt; omega))

theorem normalizedPhaseProduct_zero (m : ℕ) :
    normalizedPhaseProduct m 0 =
      ∏ ell : Fin (m - 1), (rootKappa m (ell.val + 1) + Complex.I) := by
  simp only [normalizedPhaseProduct, phaseNormalized_zero]

theorem normalizedPhaseProduct_ne_zero (m : ℕ) (hm : 1 ≤ m)
    (theta : ℝ) (htheta : theta ∈ Set.Icc 0 Real.pi) :
    normalizedPhaseProduct m theta ≠ 0 := by
  unfold normalizedPhaseProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro ell _
  have hκ := rootKappa_re_pos m (ell.val + 1) (by omega) (by have := ell.isLt; omega)
  have hpos := phaseNormalized_re_pos _ hκ theta htheta
  intro hzero
  rw [hzero, Complex.zero_re] at hpos
  exact (lt_irrefl 0) hpos

/-- Multiplication adds the individual phases inside the exponential, without branch reduction. -/
theorem normalizedPhaseProduct_polar (m : ℕ) (theta : ℝ) :
    normalizedPhaseProduct m theta =
      (‖normalizedPhaseProduct m theta‖ : ℂ) *
        Complex.exp ((manuscriptPsi m theta : ℂ) * Complex.I) := by
  let P : Fin (m - 1) → ℂ := fun ell =>
    phaseNormalized (rootKappa m (ell.val + 1)) theta
  have hnorm : (∏ ell : Fin (m - 1), (‖P ell‖ : ℂ)) =
      (‖normalizedPhaseProduct m theta‖ : ℂ) := by
    simp only [normalizedPhaseProduct, norm_prod, Complex.ofReal_prod, P]
  have hsum : (∑ ell : Fin (m - 1), ((P ell).arg : ℂ) * Complex.I) =
      (manuscriptPsi m theta : ℂ) * Complex.I := by
    rw [← Finset.sum_mul]
    simp only [manuscriptPsi, individualPhase, Complex.ofReal_sum, P]
  change (∏ ell : Fin (m - 1), P ell) = _
  calc
    (∏ ell : Fin (m - 1), P ell) =
        ∏ ell : Fin (m - 1), (‖P ell‖ : ℂ) *
          Complex.exp (((P ell).arg : ℂ) * Complex.I) := by
      apply Finset.prod_congr rfl
      intro ell _
      exact (Complex.norm_mul_exp_arg_mul_I (P ell)).symm
    _ = (∏ ell : Fin (m - 1), (‖P ell‖ : ℂ)) *
        Complex.exp (∑ ell : Fin (m - 1), ((P ell).arg : ℂ) * Complex.I) := by
      rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    _ = _ := by rw [hnorm, hsum]

theorem manuscriptPhaseProduct_factorization (m : ℕ) (theta : ℝ) :
    manuscriptPhaseProduct m theta =
      ((2 * Real.sin (theta / 2) : ℝ) : ℂ) ^ (m - 1) *
        normalizedPhaseProduct m theta := by
  have hinv : (oscillatoryRoot theta)⁻¹ =
      Complex.exp (-(theta : ℂ) * Complex.I) := by
    rw [oscillatoryRoot_inv]
    simp only [oscillatoryRoot, Complex.ofReal_neg]
  unfold manuscriptPhaseProduct
  calc
    (∏ ell : Fin (m - 1),
        (1 - stableRootCurve (rootKappa m (ell.val + 1)) theta *
          (oscillatoryRoot theta)⁻¹)) =
        ∏ ell : Fin (m - 1), ((2 * Real.sin (theta / 2) : ℝ) : ℂ) *
          phaseNormalized (rootKappa m (ell.val + 1)) theta := by
      apply Finset.prod_congr rfl
      intro ell _
      rw [hinv]
      simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using
        phase_factorization (rootKappa m (ell.val + 1)) theta
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rfl

private lemma phaseScalar_pos (theta : ℝ)
    (htheta : 0 < theta) (htheta_pi : theta ≤ Real.pi) :
    0 < 2 * Real.sin (theta / 2) :=
  mul_pos (by norm_num)
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))

theorem manuscriptPhaseProduct_ne_zero
    (m : ℕ) (hm : 1 ≤ m) (theta : ℝ)
    (htheta : 0 < theta) (htheta_pi : theta ≤ Real.pi) :
    manuscriptPhaseProduct m theta ≠ 0 := by
  rw [manuscriptPhaseProduct_factorization]
  exact mul_ne_zero
    (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (phaseScalar_pos theta htheta htheta_pi))))
    (normalizedPhaseProduct_ne_zero m hm theta ⟨htheta.le, htheta_pi⟩)

theorem manuscriptPhaseProduct_polar
    (m : ℕ) (hm : 1 ≤ m) (theta : ℝ)
    (htheta : 0 < theta) (htheta_pi : theta ≤ Real.pi) :
    manuscriptPhaseProduct m theta =
      (‖manuscriptPhaseProduct m theta‖ : ℂ) *
        Complex.exp ((manuscriptPsi m theta : ℂ) * Complex.I) := by
  have hs := phaseScalar_pos theta htheta htheta_pi
  have hnorm : ‖manuscriptPhaseProduct m theta‖ =
      (2 * Real.sin (theta / 2)) ^ (m - 1) * ‖normalizedPhaseProduct m theta‖ := by
    rw [manuscriptPhaseProduct_factorization, norm_mul, norm_pow,
      Complex.norm_of_nonneg hs.le]
  calc
    manuscriptPhaseProduct m theta =
        ((2 * Real.sin (theta / 2) : ℝ) : ℂ) ^ (m - 1) *
          normalizedPhaseProduct m theta := manuscriptPhaseProduct_factorization m theta
    _ = ((2 * Real.sin (theta / 2) : ℝ) : ℂ) ^ (m - 1) *
        ((‖normalizedPhaseProduct m theta‖ : ℂ) *
          Complex.exp ((manuscriptPsi m theta : ℂ) * Complex.I)) :=
      congrArg (fun z : ℂ => ((2 * Real.sin (theta / 2) : ℝ) : ℂ) ^ (m - 1) * z)
        (normalizedPhaseProduct_polar m theta)
    _ = _ := by
      rw [hnorm]
      push_cast
      ring

/-- Conjugation reverses the denominator phase, giving the positive doubled phase. -/
theorem manuscriptPhaseProduct_div_conj
    (m : ℕ) (hm : 1 ≤ m) (theta : ℝ)
    (htheta : 0 < theta) (htheta_pi : theta ≤ Real.pi) :
    manuscriptPhaseProduct m theta /
        (starRingEnd ℂ) (manuscriptPhaseProduct m theta) =
      Complex.exp (((2 * manuscriptPsi m theta : ℝ) : ℂ) * Complex.I) := by
  have hpolar := manuscriptPhaseProduct_polar m hm theta htheta htheta_pi
  have hnorm : (‖manuscriptPhaseProduct m theta‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr
      (manuscriptPhaseProduct_ne_zero m hm theta htheta htheta_pi))
  have hcexp : (starRingEnd ℂ)
      (Complex.exp ((manuscriptPsi m theta : ℂ) * Complex.I)) =
        Complex.exp (-((manuscriptPsi m theta : ℂ) * Complex.I)) := by
    rw [← Complex.exp_conj]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  have hconj : (starRingEnd ℂ) (manuscriptPhaseProduct m theta) =
      (‖manuscriptPhaseProduct m theta‖ : ℂ) *
        Complex.exp (-((manuscriptPsi m theta : ℂ) * Complex.I)) := by
    simpa only [map_mul, Complex.conj_ofReal, hcexp] using
      congrArg (starRingEnd ℂ) hpolar
  calc
    manuscriptPhaseProduct m theta / (starRingEnd ℂ) (manuscriptPhaseProduct m theta) =
        ((‖manuscriptPhaseProduct m theta‖ : ℂ) *
          Complex.exp ((manuscriptPsi m theta : ℂ) * Complex.I)) /
        ((‖manuscriptPhaseProduct m theta‖ : ℂ) *
          Complex.exp (-((manuscriptPsi m theta : ℂ) * Complex.I))) :=
      congrArg₂ (fun a b : ℂ => a / b) hpolar hconj
    _ = Complex.exp ((manuscriptPsi m theta : ℂ) * Complex.I) /
        Complex.exp (-((manuscriptPsi m theta : ℂ) * Complex.I)) :=
      mul_div_mul_left _ _ hnorm
    _ = Complex.exp ((manuscriptPsi m theta : ℂ) * Complex.I -
        -((manuscriptPsi m theta : ℂ) * Complex.I)) := by rw [Complex.exp_sub]
    _ = _ := by
      congr 1
      push_cast
      ring

#print axioms normalizedPhaseProduct_contDiff
#print axioms normalizedPhaseProduct_zero
#print axioms normalizedPhaseProduct_ne_zero
#print axioms normalizedPhaseProduct_polar
#print axioms manuscriptPhaseProduct_factorization
#print axioms manuscriptPhaseProduct_ne_zero
#print axioms manuscriptPhaseProduct_polar
#print axioms manuscriptPhaseProduct_div_conj

end MF21Restart
