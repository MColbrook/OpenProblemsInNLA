import MF21.ExpansionEstimates
import MF21.ActualTailAngles
import MF21.ActualTraceObstruction
import MF21.MF21CoefficientUniqueness

/-! The complete MF-21 target and the stronger all-continuous-family obstruction.
No spectral, asymptotic, mesh-density or coefficient-existence hypothesis remains.
The theorem statements use the unchanged Challenge definitions. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace MF21Verified

/-- Every actual phase model proves the complete target for its common family. -/
theorem targetAt (m : ℕ) (hm : 3 ≤ m) : MF21Challenge.TargetAt m := by
  let model := MF21Quantization.actualModel m (by omega)
  have htail := MF21Expansion.actual_tailAngleApproximation m (by omega) model
  obtain ⟨hcont, hzero, hlower, hbulk⟩ :=
    MF21Expansion.expansion_assertions_of_tailAngle m (by omega) model htail
  exact ⟨model.d, hcont, hzero, hlower, hbulk,
    MF21Obstruction.model_not_uniform m hm model⟩

/-- All three original assertions, for every m >= 3, with one common continuous
coefficient family and the exact original grid and cutoff. -/
theorem fullTarget : MF21Challenge.FullTarget := targetAt

/-- No continuous coefficient family can satisfy the forbidden next uniform
order. This follows from actual bulk existence and closed-interval uniqueness. -/
theorem universalObstruction : MF21Challenge.UniversalObstruction :=
  MF21Uniqueness.universalObstruction_of_fullTarget fullTarget

/-- The coefficient family constructed in the proof is smooth at every point
of the entire closed coefficient interval. -/
theorem smooth_coefficients (m : ℕ) (hm : 3 ≤ m) (k : ℕ)
    (x : ℝ) (hx : x ∈ Icc 0 Real.pi) :
    ContDiffAt ℝ ∞ ((MF21Quantization.actualModel m (by omega)).d k) x :=
  (MF21Quantization.actualModel m (by omega)).d_smooth k x hx

/-- The failure is witnessed in a fixed finite head in every sufficiently
large dimension, at the h^(2m) scale. -/
theorem finite_head_sharpness (m : ℕ) (hm : 3 ≤ m) :
    ∃ J : ℕ, 0 < J ∧ ∃ eps : ℝ, 0 < eps ∧
      ∀ᶠ n in atTop, ∃ j : Fin n, j.val < J ∧
        eps / ((n : ℝ) + 2) ^ (2 * m) <
          |MF21Challenge.remainder m (2 * m) n
            (MF21Quantization.actualModel m (by omega)).d j| :=
  MF21Obstruction.model_finite_head_remainder m hm _


/-- The signed-binomial matrix in the target is exactly the original Fourier
matrix, with source normalization 1/(2*pi), integration limits and exponent sign. -/
theorem fourier_matrix_entries (m n : ℕ) (i j : Fin n) :
    (MF21Challenge.toeplitz m n i j : ℂ) =
      (1 / (2 * Real.pi) : ℂ) *
        ∫ theta in -Real.pi..Real.pi,
          (MF21Challenge.symbol m theta : ℂ) *
            Complex.exp (-(((i.val : ℤ) - j.val) : ℂ) * (theta : ℂ) * Complex.I) :=
  by simpa [MF21Fourier.sourceCoefficient] using MF21Fourier.toeplitz_eq_source m n i j

/-- The uniform maximum-error upper bound at order 2m matches the scale of the
finite-head lower bound; its exponent is 2m rather than the impossible 2m+1. -/
theorem model_sharp_upper (m : ℕ) (hm : 1 ≤ m) (model : MF21Quantization.Model m) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : Fin n,
      |MF21Challenge.remainder m (2 * m) n model.d j| ≤ C / ((n : ℝ) + 2) ^ (2 * m) := by
  have htail := MF21Expansion.actual_tailAngleApproximation m (by omega) model
  obtain ⟨K, hK, N, hN⟩ := MF21Expansion.uniformModelError_of_tailSymbol m hm model
    (MF21Expansion.tailSymbol_of_tailAngle m hm model htail)
  obtain ⟨D, hD, ht⟩ := model.uniform_taylor (2 * m)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    (MF21Expansion.step_tendsto.eventually_lt_const model.Hpos)
  refine ⟨K + D, by positivity, max N N₁, ?_⟩
  intro n hn j
  have he := hN n ((le_max_left _ _).trans hn) j
  have hT := ht _ (MF21Expansion.grid_mem n j) _
    ⟨(MF21Expansion.step_pos n).le, (hN₁ n ((le_max_right _ _).trans hn)).le⟩
  have hpow := pow_le_pow_of_le_one (MF21Expansion.step_pos n).le
    (MF21Expansion.step_le_one n) (show 2 * m ≤ 2 * m + 1 by omega)
  rw [MF21Expansion.remainder_eq]
  apply (abs_add_le _ _).trans
  calc
    _ ≤ K * MF21Expansion.step n ^ (2 * m) + D * MF21Expansion.step n ^ (2 * m + 1) :=
      add_le_add he hT
    _ ≤ (K + D) * MF21Expansion.step n ^ (2 * m) := by
      nlinarith [mul_le_mul_of_nonneg_left hpow hD.le]
    _ = (K + D) / ((n : ℝ) + 2) ^ (2 * m) := by
      rw [MF21Expansion.step, inv_pow, div_eq_mul_inv]

/-- The manuscript's additional smoothness and finite-head sharpness assertions
hold for the very same family that satisfies every expansion estimate. -/
theorem smooth_common_family (m : ℕ) (hm : 3 ≤ m) :
    ∃ d : MF21Challenge.Coefficients,
      (∀ k ≤ 2 * m, ContDiffOn ℝ ∞ (d k) (Icc 0 Real.pi)) ∧
      MF21Challenge.ContinuousCoefficients m d ∧
      (∀ x ∈ Icc 0 Real.pi, d 0 x = MF21Challenge.symbol m x) ∧
      (∀ p : ℕ, p ≤ 2 * m - 1 → MF21Challenge.UniformOrder m p d) ∧
      MF21Challenge.BulkTopOrder m d ∧ ¬ MF21Challenge.UniformOrder m (2 * m) d ∧
      (∃ J : ℕ, 0 < J ∧ ∃ eps : ℝ, 0 < eps ∧
        ∀ᶠ n in atTop, ∃ j : Fin n, j.val < J ∧
          eps / ((n : ℝ) + 2) ^ (2 * m) < |MF21Challenge.remainder m (2 * m) n d j|) ∧
      (∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : Fin n,
        |MF21Challenge.remainder m (2 * m) n d j| ≤ C / ((n : ℝ) + 2) ^ (2 * m)) := by
  let model := MF21Quantization.actualModel m (by omega)
  have htail := MF21Expansion.actual_tailAngleApproximation m (by omega) model
  obtain ⟨hcont, hzero, hlower, hbulk⟩ :=
    MF21Expansion.expansion_assertions_of_tailAngle m (by omega) model htail
  exact ⟨model.d, fun k _ x hx ↦ (model.d_smooth k x hx).contDiffWithinAt,
    hcont, hzero, hlower, hbulk, MF21Obstruction.model_not_uniform m hm model,
    MF21Obstruction.model_finite_head_remainder m hm model,
    model_sharp_upper m (by omega) model⟩

end MF21Verified
#print axioms MF21Verified.targetAt
#print axioms MF21Verified.fullTarget
#print axioms MF21Verified.universalObstruction
#print axioms MF21Verified.smooth_coefficients
#print axioms MF21Verified.finite_head_sharpness

#print axioms MF21Verified.smooth_common_family
#print axioms MF21Verified.fourier_matrix_entries
#print axioms MF21Verified.model_sharp_upper
