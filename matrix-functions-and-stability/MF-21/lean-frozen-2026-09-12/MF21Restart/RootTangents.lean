import MF21Restart.CharacteristicRoots
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
The actual first derivatives at zero of the ordered characteristic roots.
Their distinctness is proved from the signs of the real parts and the
already proved root-of-unity injectivity. ROOT_TANGENTS_STATEMENTS.md
locks this ingredient in the argument following manuscript equation (18).
-/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

def characteristicRootTangents (m : ℕ) (i : Fin (2 * m)) : ℂ :=
  if i.val < m - 1 then
    -rootKappa m (i.val + 1)
  else if i.val = m - 1 then
    Complex.I
  else if i.val = m then
    -Complex.I
  else
    rootKappa m (i.val - m)

theorem oscillatoryRoot_zero : oscillatoryRoot 0 = 1 := by
  simp [oscillatoryRoot]

theorem oscillatoryRoot_hasDerivAt_zero :
    HasDerivAt oscillatoryRoot Complex.I (0 : ℝ) := by
  convert! (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const Complex.I).cexp using 1 <;>
    simp [oscillatoryRoot]

private lemma oscillatoryRoot_inv_hasDerivAt_zero :
    HasDerivAt (fun theta : ℝ => (oscillatoryRoot theta)⁻¹) (-Complex.I) 0 := by
  convert! oscillatoryRoot_hasDerivAt_zero.inv (oscillatoryRoot_ne_zero 0) using 1 <;>
    simp only [oscillatoryRoot_zero, one_pow, div_one]

private lemma stableRootCurve_inv_hasDerivAt_zero (κ : ℂ) :
    HasDerivAt (fun theta : ℝ => (stableRootCurve κ theta)⁻¹) κ 0 := by
  convert! (stableRootCurve_hasDerivAt_zero κ).inv (stableRootCurve_ne_zero κ 0) using 1 <;>
    simp only [stableRootCurve_zero, one_pow, neg_neg, div_one]

theorem characteristicRoots_zero (m : ℕ) (i : Fin (2 * m)) :
    characteristicRoots m 0 i = 1 := by
  unfold characteristicRoots
  split_ifs <;> simp only [stableRootCurve_zero, oscillatoryRoot_zero, inv_one]

theorem characteristicRoots_hasDerivAt_zero (m : ℕ) (i : Fin (2 * m)) :
    HasDerivAt (fun theta : ℝ => characteristicRoots m theta i)
      (characteristicRootTangents m i) 0 := by
  by_cases hstable : i.val < m - 1
  · simpa only [characteristicRoots, characteristicRootTangents, if_pos hstable] using
      stableRootCurve_hasDerivAt_zero (rootKappa m (i.val + 1))
  · by_cases hunit : i.val = m - 1
    · simpa only [characteristicRoots, characteristicRootTangents,
        if_neg hstable, if_pos hunit] using oscillatoryRoot_hasDerivAt_zero
    · by_cases hinverse : i.val = m
      · simpa only [characteristicRoots, characteristicRootTangents,
          if_neg hstable, if_neg hunit, if_pos hinverse] using
          oscillatoryRoot_inv_hasDerivAt_zero
      · simpa only [characteristicRoots, characteristicRootTangents,
          if_neg hstable, if_neg hunit, if_neg hinverse] using
          stableRootCurve_inv_hasDerivAt_zero (rootKappa m (i.val - m))

/-- Squaring the concrete kappa parameters recovers the distinct omega parameters. -/
theorem rootKappa_injective (m : ℕ) :
    Function.Injective (fun ell : Fin m => rootKappa m ell.val) := by
  intro a b hab
  apply rootOmega_injective m
  have hsq := congrArg (fun z : ℂ => z ^ 2) hab
  change rootKappa m a.val ^ 2 = rootKappa m b.val ^ 2 at hsq
  rw [rootKappa_sq, rootKappa_sq] at hsq
  simpa only [neg_neg] using congrArg (fun z : ℂ => -z) hsq

private lemma characteristicRootTangents_stable (m : ℕ) (i : Fin (2 * m))
    (hi : i.val < m - 1) :
    characteristicRootTangents m i = -rootKappa m (i.val + 1) := by
  simp only [characteristicRootTangents, if_pos hi]

private lemma characteristicRootTangents_unit (m : ℕ) (i : Fin (2 * m))
    (hi : i.val = m - 1) : characteristicRootTangents m i = Complex.I := by
  simp [characteristicRootTangents, hi]

private lemma characteristicRootTangents_unit_inv (m : ℕ) (hm : 2 ≤ m)
    (i : Fin (2 * m)) (hi : i.val = m) :
    characteristicRootTangents m i = -Complex.I := by
  simp [characteristicRootTangents, hi, show ¬m < m - 1 by omega,
    show m ≠ m - 1 by omega]

private lemma characteristicRootTangents_exterior (m : ℕ) (i : Fin (2 * m))
    (hi : m < i.val) :
    characteristicRootTangents m i = rootKappa m (i.val - m) := by
  simp [characteristicRootTangents, show ¬i.val < m - 1 by omega,
    show i.val ≠ m - 1 by omega, show i.val ≠ m by omega]

/-- The strict real-part signs identify the stable and exterior positions. -/
theorem characteristicRootTangents_re_regions (m : ℕ) (hm : 2 ≤ m)
    (i : Fin (2 * m)) :
    ((characteristicRootTangents m i).re < 0 ↔ i.val < m - 1) ∧
      (0 < (characteristicRootTangents m i).re ↔ m < i.val) := by
  have hi_bound := i.isLt
  by_cases hleft : i.val < m - 1
  · rw [characteristicRootTangents_stable m i hleft]
    have hpos := rootKappa_re_pos m (i.val + 1) (by omega) (by omega)
    have hneg : (-rootKappa m (i.val + 1)).re < 0 := by
      simp only [Complex.neg_re]
      linarith
    exact ⟨iff_of_true hneg hleft,
      iff_of_false (not_lt_of_ge hneg.le) (by omega)⟩
  · by_cases hunit : i.val = m - 1
    · rw [characteristicRootTangents_unit m i hunit]
      simp [hleft, show ¬m < i.val by omega]
    · by_cases hinverse : i.val = m
      · rw [characteristicRootTangents_unit_inv m hm i hinverse]
        simp [hleft, show ¬m < i.val by omega]
      · have hout : m < i.val := by omega
        rw [characteristicRootTangents_exterior m i hout]
        have hpos := rootKappa_re_pos m (i.val - m) (by omega) (by omega)
        exact ⟨iff_of_false (not_lt_of_ge hpos.le) hleft, iff_of_true hpos hout⟩

theorem characteristicRootTangents_injective (m : ℕ) (hm : 2 ≤ m) :
    Function.Injective (characteristicRootTangents m) := by
  intro a b hab
  have ha_bound := a.isLt
  have hb_bound := b.isLt
  have hre : (characteristicRootTangents m a).re = (characteristicRootTangents m b).re :=
    congrArg Complex.re hab
  have ha_regions := characteristicRootTangents_re_regions m hm a
  have hb_regions := characteristicRootTangents_re_regions m hm b
  have hleft_iff : a.val < m - 1 ↔ b.val < m - 1 := by
    rw [← ha_regions.1, ← hb_regions.1, hre]
  have hout_iff : m < a.val ↔ m < b.val := by
    rw [← ha_regions.2, ← hb_regions.2, hre]
  by_cases ha : a.val < m - 1
  · have hb : b.val < m - 1 := hleft_iff.mp ha
    rw [characteristicRootTangents_stable m a ha,
      characteristicRootTangents_stable m b hb] at hab
    have hkappa : rootKappa m (a.val + 1) = rootKappa m (b.val + 1) := by
      simpa only [neg_neg] using congrArg (fun z : ℂ => -z) hab
    have hidx : (⟨a.val + 1, by omega⟩ : Fin m) = ⟨b.val + 1, by omega⟩ :=
      rootKappa_injective m hkappa
    have hval := congrArg Fin.val hidx
    change a.val + 1 = b.val + 1 at hval
    apply Fin.ext
    omega
  · by_cases haout : m < a.val
    · have hbout : m < b.val := hout_iff.mp haout
      rw [characteristicRootTangents_exterior m a haout,
        characteristicRootTangents_exterior m b hbout] at hab
      have hidx : (⟨a.val - m, by omega⟩ : Fin m) = ⟨b.val - m, by omega⟩ :=
        rootKappa_injective m hab
      have hval := congrArg Fin.val hidx
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
        · rw [characteristicRootTangents_unit m a haunit,
            characteristicRootTangents_unit_inv m hm b hbinverse] at hab
          have him := congrArg Complex.im hab
          norm_num at him
      · rcases hb_mid with hbunit | hbinverse
        · rw [characteristicRootTangents_unit_inv m hm a hainverse,
            characteristicRootTangents_unit m b hbunit] at hab
          have him := congrArg Complex.im hab
          norm_num at him
        · apply Fin.ext
          omega

theorem characteristicRoots_sub_hasDerivAt_zero
    (m : ℕ) (a b : Fin (2 * m)) :
    HasDerivAt
      (fun theta : ℝ => characteristicRoots m theta a - characteristicRoots m theta b)
      (characteristicRootTangents m a - characteristicRootTangents m b) 0 :=
  (characteristicRoots_hasDerivAt_zero m a).sub (characteristicRoots_hasDerivAt_zero m b)

theorem characteristicRootTangents_sub_ne_zero
    (m : ℕ) (hm : 2 ≤ m) (a b : Fin (2 * m)) (hab : a ≠ b) :
    characteristicRootTangents m a - characteristicRootTangents m b ≠ 0 := by
  intro hzero
  exact hab (characteristicRootTangents_injective m hm (sub_eq_zero.mp hzero))

#print axioms characteristicRoots_zero
#print axioms characteristicRoots_hasDerivAt_zero
#print axioms characteristicRootTangents_injective
#print axioms characteristicRoots_sub_hasDerivAt_zero
#print axioms characteristicRootTangents_sub_ne_zero

end MF21Restart
