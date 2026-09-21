import MF21Restart.RootTangents
import MF21Restart.ConcreteBoundary
import MF21Restart.AnalyticSlope

/-!
Derivative-completed differences of the actual ordered characteristic
roots, and finite products of these factors. The orientation is root_j
minus root_i, as in the manuscript's Vandermonde products. Endpoint
regularity follows from the analytic slope theorem; endpoint nonvanishing
follows from the proved distinct actual tangents.
ROOT_DIFFERENCE_STATEMENTS.md fixes the scope before this proof.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

def normalizedCharacteristicDifference (m : ℕ) (i j : Fin (2 * m))
    (theta : ℝ) : ℂ :=
  dslope (fun t : ℝ => characteristicRoots m t j - characteristicRoots m t i) 0 theta

theorem normalizedCharacteristicDifference_analyticAt
    (m : ℕ) (hm : 2 ≤ m) (i j : Fin (2 * m)) (theta : ℝ) :
    AnalyticAt ℝ (normalizedCharacteristicDifference m i j) theta := by
  unfold normalizedCharacteristicDifference
  exact analyticAt_dslope_of_forall_analyticAt
    (fun t : ℝ => characteristicRoots m t j - characteristicRoots m t i)
    (fun x => ((characteristicRoots_contDiff m hm j).sub
      (characteristicRoots_contDiff m hm i)).contDiffAt.analyticAt) theta

theorem normalizedCharacteristicDifference_contDiff
    (m : ℕ) (hm : 2 ≤ m) (i j : Fin (2 * m)) :
    ContDiff ℝ ⊤ (normalizedCharacteristicDifference m i j) := by
  apply contDiff_iff_contDiffAt.mpr
  intro theta
  exact (normalizedCharacteristicDifference_analyticAt m hm i j theta).contDiffAt

theorem normalizedCharacteristicDifference_zero
    (m : ℕ) (i j : Fin (2 * m)) :
    normalizedCharacteristicDifference m i j 0 =
      characteristicRootTangents m j - characteristicRootTangents m i := by
  rw [normalizedCharacteristicDifference, dslope_same]
  exact (characteristicRoots_sub_hasDerivAt_zero m j i).deriv

/-- The completed slope agrees with literal complex division away from zero. -/
theorem normalizedCharacteristicDifference_eq_inv_mul
    (m : ℕ) (i j : Fin (2 * m)) (theta : ℝ) (htheta : theta ≠ 0) :
    normalizedCharacteristicDifference m i j theta =
      (theta : ℂ)⁻¹ * (characteristicRoots m theta j - characteristicRoots m theta i) := by
  rw [normalizedCharacteristicDifference, dslope_of_ne _ htheta, slope_def_module]
  simp only [sub_zero, characteristicRoots_zero, sub_self, Complex.real_smul,
    Complex.ofReal_inv]

/-- This identity also holds at zero, where every actual root has value one. -/
theorem characteristicRoots_sub_eq_mul_normalizedDifference
    (m : ℕ) (i j : Fin (2 * m)) (theta : ℝ) :
    characteristicRoots m theta j - characteristicRoots m theta i =
      (theta : ℂ) * normalizedCharacteristicDifference m i j theta := by
  have h := sub_smul_dslope
    (fun t : ℝ => characteristicRoots m t j - characteristicRoots m t i) 0 theta
  simpa only [normalizedCharacteristicDifference, sub_zero, characteristicRoots_zero,
    sub_self, Complex.real_smul] using h.symm

theorem normalizedCharacteristicDifference_zero_ne_zero
    (m : ℕ) (hm : 2 ≤ m) (i j : Fin (2 * m)) (hij : i ≠ j) :
    normalizedCharacteristicDifference m i j 0 ≠ 0 := by
  rw [normalizedCharacteristicDifference_zero]
  exact characteristicRootTangents_sub_ne_zero m hm j i (Ne.symm hij)

theorem normalizedCharacteristicDifference_ne_zero
    (m : ℕ) (hm : 2 ≤ m) (i j : Fin (2 * m)) (hij : i ≠ j)
    (theta : ℝ) (htheta : 0 < theta) (htheta_pi : theta < Real.pi) :
    normalizedCharacteristicDifference m i j theta ≠ 0 := by
  intro hzero
  have hdiff := characteristicRoots_sub_eq_mul_normalizedDifference m i j theta
  rw [hzero, mul_zero] at hdiff
  exact hij ((characteristicRoots_injective m hm theta htheta htheta_pi
    (sub_eq_zero.mp hdiff)).symm)

def normalizedCharacteristicDifferenceProduct (m : ℕ)
    (pairs : Finset (Fin (2 * m) × Fin (2 * m))) (theta : ℝ) : ℂ :=
  ∏ p ∈ pairs, normalizedCharacteristicDifference m p.1 p.2 theta

theorem normalizedCharacteristicDifferenceProduct_analyticAt
    (m : ℕ) (hm : 2 ≤ m) (pairs : Finset (Fin (2 * m) × Fin (2 * m)))
    (theta : ℝ) :
    AnalyticAt ℝ (normalizedCharacteristicDifferenceProduct m pairs) theta := by
  unfold normalizedCharacteristicDifferenceProduct
  exact pairs.analyticAt_fun_prod (fun p _ =>
    normalizedCharacteristicDifference_analyticAt m hm p.1 p.2 theta)

theorem normalizedCharacteristicDifferenceProduct_contDiff
    (m : ℕ) (hm : 2 ≤ m) (pairs : Finset (Fin (2 * m) × Fin (2 * m))) :
    ContDiff ℝ ⊤ (normalizedCharacteristicDifferenceProduct m pairs) := by
  apply contDiff_iff_contDiffAt.mpr
  intro theta
  exact (normalizedCharacteristicDifferenceProduct_analyticAt m hm pairs theta).contDiffAt

theorem normalizedCharacteristicDifferenceProduct_zero
    (m : ℕ) (pairs : Finset (Fin (2 * m) × Fin (2 * m))) :
    normalizedCharacteristicDifferenceProduct m pairs 0 =
      ∏ p ∈ pairs, (characteristicRootTangents m p.2 - characteristicRootTangents m p.1) := by
  unfold normalizedCharacteristicDifferenceProduct
  apply Finset.prod_congr rfl
  intro p _
  exact normalizedCharacteristicDifference_zero m p.1 p.2

theorem normalizedCharacteristicDifferenceProduct_zero_ne_zero
    (m : ℕ) (hm : 2 ≤ m) (pairs : Finset (Fin (2 * m) × Fin (2 * m)))
    (hpairs : ∀ p ∈ pairs, p.1 ≠ p.2) :
    normalizedCharacteristicDifferenceProduct m pairs 0 ≠ 0 := by
  unfold normalizedCharacteristicDifferenceProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact normalizedCharacteristicDifference_zero_ne_zero m hm p.1 p.2 (hpairs p hp)

theorem normalizedCharacteristicDifferenceProduct_ne_zero
    (m : ℕ) (hm : 2 ≤ m) (pairs : Finset (Fin (2 * m) × Fin (2 * m)))
    (hpairs : ∀ p ∈ pairs, p.1 ≠ p.2)
    (theta : ℝ) (htheta : 0 < theta) (htheta_pi : theta < Real.pi) :
    normalizedCharacteristicDifferenceProduct m pairs theta ≠ 0 := by
  unfold normalizedCharacteristicDifferenceProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact normalizedCharacteristicDifference_ne_zero m hm p.1 p.2 (hpairs p hp)
    theta htheta htheta_pi

theorem characteristicRoots_differenceProduct_eq_pow_mul
    (m : ℕ) (pairs : Finset (Fin (2 * m) × Fin (2 * m))) (theta : ℝ) :
    (∏ p ∈ pairs, (characteristicRoots m theta p.2 - characteristicRoots m theta p.1)) =
      (theta : ℂ) ^ pairs.card * normalizedCharacteristicDifferenceProduct m pairs theta := by
  calc
    (∏ p ∈ pairs, (characteristicRoots m theta p.2 - characteristicRoots m theta p.1)) =
        ∏ p ∈ pairs, (theta : ℂ) * normalizedCharacteristicDifference m p.1 p.2 theta := by
      apply Finset.prod_congr rfl
      intro p _
      exact characteristicRoots_sub_eq_mul_normalizedDifference m p.1 p.2 theta
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      rfl

#print axioms normalizedCharacteristicDifference_analyticAt
#print axioms normalizedCharacteristicDifference_contDiff
#print axioms normalizedCharacteristicDifference_zero
#print axioms characteristicRoots_sub_eq_mul_normalizedDifference
#print axioms normalizedCharacteristicDifference_zero_ne_zero
#print axioms normalizedCharacteristicDifference_ne_zero
#print axioms normalizedCharacteristicDifferenceProduct_analyticAt
#print axioms normalizedCharacteristicDifferenceProduct_contDiff
#print axioms normalizedCharacteristicDifferenceProduct_zero
#print axioms normalizedCharacteristicDifferenceProduct_zero_ne_zero
#print axioms normalizedCharacteristicDifferenceProduct_ne_zero
#print axioms characteristicRoots_differenceProduct_eq_pow_mul

end MF21Restart
