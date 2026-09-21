import MF21Restart.VandermondeScale
import MF21Restart.RootTangents
import MF21Restart.ConcreteBoundary
import MF21Restart.AnalyticSlope

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

def characteristicRootSlope (m : ℕ) (i : Fin (2 * m)) (θ : ℝ) : ℂ :=
  dslope (fun t : ℝ => characteristicRoots m t i) 0 θ

theorem characteristicRootSlope_analyticAt (m : ℕ) (hm : 2 ≤ m)
    (i : Fin (2 * m)) (θ : ℝ) : AnalyticAt ℝ (characteristicRootSlope m i) θ :=
  analyticAt_dslope_of_forall_analyticAt _
    (fun _ => (characteristicRoots_contDiff m hm i).contDiffAt.analyticAt) θ

theorem characteristicRootSlope_contDiff (m : ℕ) (hm : 2 ≤ m) (i : Fin (2 * m)) :
    ContDiff ℝ ⊤ (characteristicRootSlope m i) :=
  contDiff_iff_contDiffAt.mpr fun θ => (characteristicRootSlope_analyticAt m hm i θ).contDiffAt

theorem characteristicRootSlope_zero (m : ℕ) (i : Fin (2 * m)) :
    characteristicRootSlope m i 0 = characteristicRootTangents m i := by
  rw [characteristicRootSlope, dslope_same]
  exact (characteristicRoots_hasDerivAt_zero m i).deriv

theorem characteristicRoots_eq_one_add_mul_slope (m : ℕ) (i : Fin (2 * m)) (θ : ℝ) :
    characteristicRoots m θ i = 1 + (θ : ℂ) * characteristicRootSlope m i θ := by
  have h := sub_smul_dslope (fun t : ℝ => characteristicRoots m t i) 0 θ
  simp only [sub_zero, characteristicRoots_zero, Complex.real_smul] at h
  change (θ : ℂ) * characteristicRootSlope m i θ = characteristicRoots m θ i - 1 at h
  rw [h]
  ring

def normalizedRootVandermonde (m k : ℕ) (u : Fin k → Fin (2 * m)) (θ : ℝ) : ℂ :=
  (Matrix.vandermonde (fun i => characteristicRootSlope m (u i) θ)).det

theorem normalizedRootVandermonde_contDiff (m k : ℕ) (hm : 2 ≤ m)
    (u : Fin k → Fin (2 * m)) : ContDiff ℝ ⊤ (normalizedRootVandermonde m k u) := by
  have heq : normalizedRootVandermonde m k u = fun θ =>
      ∏ i : Fin k, ∏ j ∈ Finset.Ioi i,
        (characteristicRootSlope m (u j) θ - characteristicRootSlope m (u i) θ) := by
    funext θ
    exact Matrix.det_vandermonde _
  rw [heq]
  apply contDiff_prod
  intro i _
  apply contDiff_prod
  intro j _
  exact (characteristicRootSlope_contDiff m hm (u j)).sub
    (characteristicRootSlope_contDiff m hm (u i))

theorem rootVandermonde_eq_pow_mul_normalized (m k : ℕ)
    (u : Fin k → Fin (2 * m)) (θ : ℝ) :
    (Matrix.vandermonde (fun i => characteristicRoots m θ (u i))).det =
      (θ : ℂ) ^ vandermondeDegree k * normalizedRootVandermonde m k u θ := by
  have heq : (fun i => characteristicRoots m θ (u i)) =
      (fun i => 1 + (θ : ℂ) * characteristicRootSlope m (u i) θ) := by
    funext i
    exact characteristicRoots_eq_one_add_mul_slope m (u i) θ
  rw [heq, vandermonde_one_add_mul]
  rfl

theorem normalizedRootVandermonde_zero_ne_zero (m k : ℕ) (hm : 2 ≤ m)
    (u : Fin k → Fin (2 * m)) (hu : Function.Injective u) :
    normalizedRootVandermonde m k u 0 ≠ 0 := by
  unfold normalizedRootVandermonde
  simp only [characteristicRootSlope_zero]
  exact Matrix.det_vandermonde_ne_zero_iff.mpr
    ((characteristicRootTangents_injective m hm).comp hu)

def normalizedBoundaryCoefficient (m : ℕ) (s : Finset (Fin (2 * m)))
    (hs : s.card = m) (θ : ℝ) : ℂ :=
  (↑↑(boundaryLaplaceSign m s hs) : ℂ) *
    normalizedRootVandermonde m m (sᶜ.orderEmbOfFin (boundary_compl_card hs)) θ *
    normalizedRootVandermonde m m (s.orderEmbOfFin hs) θ

theorem boundaryCoefficient_eq_pow_mul_normalized (m : ℕ)
    (s : Finset (Fin (2 * m))) (hs : s.card = m) (θ : ℝ) :
    boundaryCoefficient m (characteristicRoots m θ) s =
      (θ : ℂ) ^ (m * (m - 1)) * normalizedBoundaryCoefficient m s hs θ := by
  rw [boundaryCoefficient_vandermonde m _ s hs,
    rootVandermonde_eq_pow_mul_normalized, rootVandermonde_eq_pow_mul_normalized]
  have hp : (θ : ℂ) ^ (m * (m - 1)) =
      (θ : ℂ) ^ vandermondeDegree m * (θ : ℂ) ^ vandermondeDegree m := by
    rw [← twice_vandermondeDegree, two_mul, pow_add]
  rw [hp]
  unfold normalizedBoundaryCoefficient
  ring

theorem normalizedBoundaryCoefficient_contDiff (m : ℕ) (hm : 2 ≤ m)
    (s : Finset (Fin (2 * m))) (hs : s.card = m) :
    ContDiff ℝ ⊤ (normalizedBoundaryCoefficient m s hs) :=
  (contDiff_const.mul (normalizedRootVandermonde_contDiff m m hm _)).mul
    (normalizedRootVandermonde_contDiff m m hm _)

theorem normalizedBoundaryCoefficient_zero_ne_zero (m : ℕ) (hm : 2 ≤ m)
    (s : Finset (Fin (2 * m))) (hs : s.card = m) :
    normalizedBoundaryCoefficient m s hs 0 ≠ 0 := by
  have hsign : (↑↑(boundaryLaplaceSign m s hs) : ℂ) ≠ 0 := by
    rcases Int.units_eq_one_or (boundaryLaplaceSign m s hs) with h | h <;> simp [h]
  exact mul_ne_zero (mul_ne_zero hsign
    (normalizedRootVandermonde_zero_ne_zero m m hm _
      (sᶜ.orderEmbOfFin (boundary_compl_card hs)).injective))
    (normalizedRootVandermonde_zero_ne_zero m m hm _ (s.orderEmbOfFin hs).injective)

#print axioms characteristicRootSlope_analyticAt
#print axioms characteristicRootSlope_contDiff
#print axioms characteristicRootSlope_zero
#print axioms characteristicRoots_eq_one_add_mul_slope
#print axioms normalizedRootVandermonde_contDiff
#print axioms rootVandermonde_eq_pow_mul_normalized
#print axioms normalizedRootVandermonde_zero_ne_zero
#print axioms boundaryCoefficient_eq_pow_mul_normalized
#print axioms normalizedBoundaryCoefficient_contDiff
#print axioms normalizedBoundaryCoefficient_zero_ne_zero

end MF21Restart
