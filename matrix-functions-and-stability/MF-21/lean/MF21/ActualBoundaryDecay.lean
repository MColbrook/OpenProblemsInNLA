import MF21.BoundaryDecay
import MF21.BulkDecay
import MF21.BulkSlopes

/-! Uniform decay for every actual nonleading geometric boundary term. -/
noncomputable section
open scoped BigOperators
open Finset Set
namespace MF21ActualBoundary
open MF21Bulk MF21Normalization

theorem baseRoot_norm_le_one (m : ℕ) (hm : 0 < m) (theta : ℝ)
    (ht : theta ∈ Ioc 0 Real.pi) (j : Fin m) : ‖baseRoot m theta j‖ ≤ 1 := by
  by_cases hj : j.val=0
  · simp [baseRoot, hj, unitRoot_norm]
  · simpa only [baseRoot, if_neg hj] using
      (stableRoot_spec (omega m j) (spectralBase theta)
        (spectralBase_pos_of_mem theta ht) (omega_norm m j)
        (omega_ne_one m hm j hj)).2.1.le

/-- One positive decay constant works for the whole finite stable-root family. -/
theorem stable_family_exp_bound (m : ℕ) (hm : 0 < m) :
    ∃ c : ℝ, 0<c ∧ ∀ theta ∈ Ioc 0 Real.pi, ∀ j : Fin m, j.val ≠ 0 →
      ‖baseRoot m theta j‖ ≤ Real.exp (-c*theta) := by
  classical
  have hc : ∀ j : Fin m, ∃ c : ℝ, 0<c ∧ ∀ theta ∈ Ioc 0 Real.pi,
      j.val ≠ 0 → ‖baseRoot m theta j‖ ≤ Real.exp (-c*theta) := by
    intro j
    by_cases hj : j.val=0
    · exact ⟨1, by norm_num, fun _ _ h => (h hj).elim⟩
    · obtain ⟨c, hc, hbound⟩ := stableRoot_angle_exp_bound (omega m j) (kappa m j)
        (omega_norm m j) (omega_ne_one m hm j hj) (kappa_sq m j) (kappa_re_pos m hm j hj)
      exact ⟨c, hc, fun theta ht _ => by simpa [baseRoot, hj] using hbound theta ht⟩
  choose c hc hbound using hc
  obtain ⟨j₀, _, hmin⟩ := univ.exists_min_image c ⟨⟨0, hm⟩, mem_univ _⟩
  refine ⟨c j₀, hc j₀, ?_⟩
  intro theta ht j hj
  exact (hbound j theta ht hj).trans (Real.exp_le_exp.mpr (by
    have h := hmin j (mem_univ j)
    nlinarith [ht.1]))

/-- The denominator includes the reciprocal unit root. Its modulus is exactly
that of the product of all exterior roots. -/
def rightProduct (m : ℕ) (theta : ℝ) : ℂ :=
  ∏ i : Fin m, (baseRoot m theta i)⁻¹

theorem rightProduct_ne_zero (m : ℕ) (hm : 0<m) (theta : ℝ)
    (ht : theta ∈ Ioc 0 Real.pi) : rightProduct m theta ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  intro j _
  exact inv_ne_zero ((baseRoot_spec_of_pos m hm theta (spectralBase_pos_of_mem theta ht) j).1)

/-- No spectral or asymptotic hypothesis remains in the geometric decay bound. -/
theorem nonleading_actual_exp_bound (m : ℕ) (hm : 0<m) :
    ∃ c : ℝ, 0<c ∧ ∀ theta ∈ Ioc 0 Real.pi,
      ∀ σ : Equiv.Perm (Fin m ⊕ Fin m),
      ¬selects m (fun j => j.isRight) σ →
      ¬selects m (fun j =>
        (Equiv.swap (Sum.inl (⟨0,hm⟩ : Fin m)) (Sum.inr (⟨0,hm⟩ : Fin m)) j).isRight) σ →
      ‖permutationBase m (blockRootFamily m theta) σ / rightProduct m theta‖ ≤
        Real.exp (-c*theta) := by
  obtain ⟨c, hc, hbound⟩ := stable_family_exp_bound m hm
  refine ⟨c, hc, ?_⟩
  intro theta ht σ hP hQ
  apply nonleading_base_ratio_norm_le m ⟨0,hm⟩ (baseRoot m theta)
    (fun j => (baseRoot_spec_of_pos m hm theta (spectralBase_pos_of_mem theta ht) j).1)
    (baseRoot_norm_le_one m hm theta ht) (Real.exp (-c*theta)) _ σ hP hQ
  intro j hj
  exact hbound theta ht j (by intro he; apply hj; exact Fin.ext he)

end MF21ActualBoundary
#print axioms MF21ActualBoundary.stable_family_exp_bound
#print axioms MF21ActualBoundary.nonleading_actual_exp_bound
