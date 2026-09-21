import MF21Restart.StableRootSymmetry
import MF21Restart.FourierStencil

/-!
The literal ordered list from the manuscript before equation (13):
r_1,...,r_(m-1), z, z⁻¹, r_1⁻¹,...,r_(m-1)⁻¹. Its nonvanishing,
distinctness and characteristic equations are proved for the actual
root curves. CHARACTERISTIC_ROOTS_STATEMENTS.md fixes the exact scope.
-/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

def oscillatoryRoot (theta : ℝ) : ℂ :=
  Complex.exp ((theta : ℂ) * Complex.I)

def characteristicRoots (m : ℕ) (theta : ℝ) (i : Fin (2 * m)) : ℂ :=
  if i.val < m - 1 then
    stableRootCurve (rootKappa m (i.val + 1)) theta
  else if i.val = m - 1 then
    oscillatoryRoot theta
  else if i.val = m then
    (oscillatoryRoot theta)⁻¹
  else
    (stableRootCurve (rootKappa m (i.val - m)) theta)⁻¹

theorem oscillatoryRoot_ne_zero (theta : ℝ) : oscillatoryRoot theta ≠ 0 :=
  Complex.exp_ne_zero _

theorem oscillatoryRoot_norm (theta : ℝ) : ‖oscillatoryRoot theta‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I theta

theorem oscillatoryRoot_inv (theta : ℝ) :
    (oscillatoryRoot theta)⁻¹ = oscillatoryRoot (-theta) := by
  simp only [oscillatoryRoot, Complex.ofReal_neg, neg_mul, Complex.exp_neg]

theorem oscillatoryRoot_ne_inv (theta : ℝ)
    (htheta : 0 < theta) (htheta_pi : theta < Real.pi) :
    oscillatoryRoot theta ≠ (oscillatoryRoot theta)⁻¹ := by
  intro h
  have him := congrArg Complex.im h
  rw [oscillatoryRoot_inv] at him
  simp only [oscillatoryRoot, Complex.exp_ofReal_mul_I_im, Real.sin_neg] at him
  have hs := Real.sin_pos_of_pos_of_lt_pi htheta htheta_pi
  linarith

theorem oscillatoryRoot_equation (theta : ℝ) :
    2 - oscillatoryRoot theta - (oscillatoryRoot theta)⁻¹ =
      ((2 - 2 * Real.cos theta : ℝ) : ℂ) := by
  rw [oscillatoryRoot_inv]
  simp only [oscillatoryRoot, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

theorem characteristicRoots_stable (m : ℕ) (theta : ℝ) (i : Fin (2 * m))
    (hi : i.val < m - 1) :
    characteristicRoots m theta i = stableRootCurve (rootKappa m (i.val + 1)) theta := by
  simp only [characteristicRoots, if_pos hi]

theorem characteristicRoots_unit (m : ℕ) (theta : ℝ) (i : Fin (2 * m))
    (hi : i.val = m - 1) : characteristicRoots m theta i = oscillatoryRoot theta := by
  simp [characteristicRoots, hi]

theorem characteristicRoots_unit_inv (m : ℕ) (hm : 2 ≤ m) (theta : ℝ)
    (i : Fin (2 * m)) (hi : i.val = m) :
    characteristicRoots m theta i = (oscillatoryRoot theta)⁻¹ := by
  simp [characteristicRoots, hi, show ¬m < m - 1 by omega,
    show m ≠ m - 1 by omega]

theorem characteristicRoots_exterior (m : ℕ) (theta : ℝ) (i : Fin (2 * m))
    (hi : m < i.val) :
    characteristicRoots m theta i = (stableRootCurve (rootKappa m (i.val - m)) theta)⁻¹ := by
  simp [characteristicRoots, show ¬i.val < m - 1 by omega,
    show i.val ≠ m - 1 by omega, show i.val ≠ m by omega]

theorem characteristicRoots_ne_zero
    (m : ℕ) (theta : ℝ) (i : Fin (2 * m)) :
    characteristicRoots m theta i ≠ 0 := by
  unfold characteristicRoots
  split_ifs
  · exact stableRootCurve_ne_zero _ _
  · exact oscillatoryRoot_ne_zero _
  · exact inv_ne_zero (oscillatoryRoot_ne_zero _)
  · exact inv_ne_zero (stableRootCurve_ne_zero _ _)

private lemma stable_index_norm_lt_one (m ell : ℕ)
    (hell : 1 ≤ ell) (hellm : ell < m) (theta : ℝ)
    (htheta : 0 < theta) (htheta_pi : theta ≤ Real.pi) :
    ‖stableRootCurve (rootKappa m ell) theta‖ < 1 :=
  stableRootCurve_norm_lt_one _ (rootKappa_re_pos m ell hell hellm)
    theta htheta htheta_pi

private lemma exterior_index_norm_gt_one (m ell : ℕ)
    (hell : 1 ≤ ell) (hellm : ell < m) (theta : ℝ)
    (htheta : 0 < theta) (htheta_pi : theta ≤ Real.pi) :
    1 < ‖(stableRootCurve (rootKappa m ell) theta)⁻¹‖ := by
  rw [norm_inv]
  exact (one_lt_inv₀ (norm_pos_iff.mpr (stableRootCurve_ne_zero _ _))).2
    (stable_index_norm_lt_one m ell hell hellm theta htheta htheta_pi)

/-- The two strict norm regions identify the stable and exterior positions. -/
theorem characteristicRoots_norm_regions (m : ℕ) (hm : 2 ≤ m) (theta : ℝ)
    (htheta : 0 < theta) (htheta_pi : theta ≤ Real.pi) (i : Fin (2 * m)) :
    (‖characteristicRoots m theta i‖ < 1 ↔ i.val < m - 1) ∧
      (1 < ‖characteristicRoots m theta i‖ ↔ m < i.val) := by
  have hi_bound := i.isLt
  by_cases hleft : i.val < m - 1
  · rw [characteristicRoots_stable m theta i hleft]
    have hnorm := stable_index_norm_lt_one m (i.val + 1) (by omega) (by omega)
      theta htheta htheta_pi
    exact ⟨iff_of_true hnorm hleft,
      iff_of_false (not_lt_of_ge hnorm.le) (by omega)⟩
  · by_cases hunit : i.val = m - 1
    · rw [characteristicRoots_unit m theta i hunit]
      simp [oscillatoryRoot_norm, hleft, show ¬m < i.val by omega]
    · by_cases hinverse : i.val = m
      · rw [characteristicRoots_unit_inv m hm theta i hinverse]
        simp [norm_inv, oscillatoryRoot_norm, hleft, show ¬m < i.val by omega]
      · have hout : m < i.val := by omega
        rw [characteristicRoots_exterior m theta i hout]
        have hnorm := exterior_index_norm_gt_one m (i.val - m) (by omega) (by omega)
          theta htheta htheta_pi
        exact ⟨iff_of_false (not_lt_of_ge hnorm.le) hleft, iff_of_true hnorm hout⟩

theorem characteristicRoots_injective
    (m : ℕ) (hm : 2 ≤ m) (theta : ℝ)
    (htheta : 0 < theta) (htheta_pi : theta < Real.pi) :
    Function.Injective (characteristicRoots m theta) := by
  intro a b hab
  have ha_bound := a.isLt
  have hb_bound := b.isLt
  have hnorm : ‖characteristicRoots m theta a‖ = ‖characteristicRoots m theta b‖ :=
    congrArg norm hab
  have ha_regions := characteristicRoots_norm_regions m hm theta htheta htheta_pi.le a
  have hb_regions := characteristicRoots_norm_regions m hm theta htheta htheta_pi.le b
  have hleft_iff : a.val < m - 1 ↔ b.val < m - 1 := by
    rw [← ha_regions.1, ← hb_regions.1, hnorm]
  have hout_iff : m < a.val ↔ m < b.val := by
    rw [← ha_regions.2, ← hb_regions.2, hnorm]
  by_cases ha : a.val < m - 1
  · have hb : b.val < m - 1 := hleft_iff.mp ha
    rw [characteristicRoots_stable m theta a ha,
      characteristicRoots_stable m theta b hb] at hab
    have hidx :
        (⟨a.val + 1, ⟨by omega, by omega⟩⟩ : {ell : ℕ // 1 ≤ ell ∧ ell < m}) =
          ⟨b.val + 1, ⟨by omega, by omega⟩⟩ :=
      stableRootCurve_rootKappa_injective m theta htheta htheta_pi.le hab
    have hval := congrArg Subtype.val hidx
    change a.val + 1 = b.val + 1 at hval
    apply Fin.ext
    omega
  · by_cases haout : m < a.val
    · have hbout : m < b.val := hout_iff.mp haout
      rw [characteristicRoots_exterior m theta a haout,
        characteristicRoots_exterior m theta b hbout] at hab
      have hroot : stableRootCurve (rootKappa m (a.val - m)) theta =
          stableRootCurve (rootKappa m (b.val - m)) theta := inv_inj.mp hab
      have hidx :
          (⟨a.val - m, ⟨by omega, by omega⟩⟩ : {ell : ℕ // 1 ≤ ell ∧ ell < m}) =
            ⟨b.val - m, ⟨by omega, by omega⟩⟩ :=
        stableRootCurve_rootKappa_injective m theta htheta htheta_pi.le hroot
      have hval := congrArg Subtype.val hidx
      change a.val - m = b.val - m at hval
      apply Fin.ext
      omega
    · have hb : ¬b.val < m - 1 := fun h => ha (hleft_iff.mpr h)
      have hbout : ¬m < b.val := fun h => haout (hout_iff.mpr h)
      have ha_mid : a.val = m - 1 ∨ a.val = m := by omega
      have hb_mid : b.val = m - 1 ∨ b.val = m := by omega
      rcases ha_mid with haunit | hainverse
      · rcases hb_mid with hbunit | hbinverse
        · apply Fin.ext
          omega
        · rw [characteristicRoots_unit m theta a haunit,
            characteristicRoots_unit_inv m hm theta b hbinverse] at hab
          exact False.elim (oscillatoryRoot_ne_inv theta htheta htheta_pi hab)
      · rcases hb_mid with hbunit | hbinverse
        · rw [characteristicRoots_unit_inv m hm theta a hainverse,
            characteristicRoots_unit m theta b hbunit] at hab
          exact False.elim (oscillatoryRoot_ne_inv theta htheta htheta_pi hab.symm)
        · apply Fin.ext
          omega

private lemma reciprocal_expression_inv (w : ℂ) :
    2 - w⁻¹ - (w⁻¹)⁻¹ = 2 - w - w⁻¹ := by
  rw [inv_inv]
  ring

private lemma stable_index_characteristic_equation
    (m ell : ℕ) (hm : 1 ≤ m) (theta : ℝ) :
    (2 - stableRootCurve (rootKappa m ell) theta -
      (stableRootCurve (rootKappa m ell) theta)⁻¹) ^ m = (symbol m theta : ℂ) := by
  rw [stableRootCurve_rootOmega_equation, mul_pow, rootOmega_pow m ell hm, one_mul,
    symbol_eq_cosine_power, Complex.ofReal_pow]

private lemma oscillatoryRoot_characteristic_equation (m : ℕ) (theta : ℝ) :
    (2 - oscillatoryRoot theta - (oscillatoryRoot theta)⁻¹) ^ m =
      (symbol m theta : ℂ) := by
  rw [oscillatoryRoot_equation, symbol_eq_cosine_power, Complex.ofReal_pow]

theorem characteristicRoots_equation
    (m : ℕ) (hm : 2 ≤ m) (theta : ℝ) (i : Fin (2 * m)) :
    (2 - characteristicRoots m theta i - (characteristicRoots m theta i)⁻¹) ^ m =
      (symbol m theta : ℂ) := by
  unfold characteristicRoots
  split_ifs
  · exact stable_index_characteristic_equation m (i.val + 1) (by omega) theta
  · exact oscillatoryRoot_characteristic_equation m theta
  · rw [reciprocal_expression_inv]
    exact oscillatoryRoot_characteristic_equation m theta
  · rw [reciprocal_expression_inv]
    exact stable_index_characteristic_equation m (i.val - m) (by omega) theta

#print axioms characteristicRoots_ne_zero
#print axioms characteristicRoots_norm_regions
#print axioms characteristicRoots_injective
#print axioms characteristicRoots_equation

end MF21Restart
