import MF21Restart.SpectralEnclosure
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.Pairwise
import Mathlib.Topology.Order.IntermediateValue

/-!
The actual symbol order, actual sorted spectrum, and unique interior
angle for every original in-range eigenvalue. No eigenangle choice or
phase-label identification is introduced. See `SPECTRAL_ORDER_STATEMENTS.md`.
-/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

theorem symbol_zero (m : ℕ) (hm : 1 ≤ m) : symbol m 0 = 0 := by
  have hm0 : m ≠ 0 := by omega
  simp [symbol_eq_cosine_power, hm0]

theorem symbol_pi (m : ℕ) : symbol m Real.pi = (4 : ℝ) ^ m := by
  norm_num [symbol_eq_cosine_power, Real.cos_pi]

theorem symbol_strictMonoOn (m : ℕ) (hm : 1 ≤ m) :
    StrictMonoOn (symbol m) (Set.Icc 0 Real.pi) := by
  intro x hx y hy hxy
  rw [symbol_eq_cosine_power, symbol_eq_cosine_power]
  have hcos : Real.cos y < Real.cos x := Real.strictAntiOn_cos hx hy hxy
  have hbase : 2 - 2 * Real.cos x < 2 - 2 * Real.cos y := by linarith
  have hnonneg : 0 ≤ 2 - 2 * Real.cos x := by linarith [Real.cos_le_one x]
  exact pow_lt_pow_left₀ hbase hnonneg (by omega : m ≠ 0)

/-- This order is inherited from the existing sorted list, with repeated
eigenvalues retained. -/
theorem orderedEigenvalue_monotone (m n : ℕ) : Monotone (orderedEigenvalue m n) := by
  have hsort : (orderedEigenvalueList m n).Pairwise (fun a b : ℝ => a ≤ b) := by
    unfold orderedEigenvalueList
    exact Multiset.pairwise_sort _ _
  intro i j hij
  unfold orderedEigenvalue
  apply hsort.rel_get_of_le
  change i.val ≤ j.val
  exact hij

/-- Strict spectral enclosure and the actual symbol give a unique angle
for each original one-based index. No totalized out-of-range value is used. -/
theorem eigenvalue_existsUnique_angle
    (m n j : ℕ) (hm : 1 ≤ m) (hj : 1 ≤ j) (hjn : j ≤ n) :
    ∃! θ : ℝ, θ ∈ Set.Ioo 0 Real.pi ∧ symbol m θ = eigenvalue m n j := by
  have hspec := eigenvalue_strict_spectral_enclosure m n j hm hj hjn
  have hcont : ContinuousOn (symbol m) (Set.Icc 0 Real.pi) := by
    have hg : Continuous (symbol m) := by unfold symbol; fun_prop
    exact hg.continuousOn
  have hmem : eigenvalue m n j ∈ Set.Icc (symbol m 0) (symbol m Real.pi) := by
    rw [symbol_zero m hm, symbol_pi m]
    exact ⟨hspec.1.le, hspec.2.le⟩
  obtain ⟨θ, hθ, hvalue⟩ := intermediate_value_Icc Real.pi_pos.le hcont hmem
  have hθ0 : θ ≠ 0 := by
    intro hzero
    rw [hzero, symbol_zero m hm] at hvalue
    linarith only [hspec.1, hvalue]
  have hθπ : θ ≠ Real.pi := by
    intro hpi
    rw [hpi, symbol_pi m] at hvalue
    linarith only [hspec.2, hvalue]
  have hθint : θ ∈ Set.Ioo 0 Real.pi :=
    ⟨lt_of_le_of_ne hθ.1 (Ne.symm hθ0), lt_of_le_of_ne hθ.2 hθπ⟩
  refine ⟨θ, ⟨hθint, hvalue⟩, ?_⟩
  intro φ hφ
  exact (symbol_strictMonoOn m hm).injOn
    ⟨hφ.1.1.le, hφ.1.2.le⟩ hθ (hφ.2.trans hvalue.symm)

#print axioms symbol_zero
#print axioms symbol_pi
#print axioms symbol_strictMonoOn
#print axioms orderedEigenvalue_monotone
#print axioms eigenvalue_existsUnique_angle

end MF21Restart
