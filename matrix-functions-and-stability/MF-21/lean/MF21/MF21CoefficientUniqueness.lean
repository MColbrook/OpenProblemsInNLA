import MF21.CoefficientUniqueness
import MF21.LogSquaredMesh
import MF21.Definitions

/-!
Complete uniqueness repair for the MF-21 mesh and logarithmic-squared cutoff.
Only continuity on [0,pi] and the single stated top-order uniform bound are
assumed. There are no hypotheses for lower truncation orders, mesh density,
endpoint extension, or ambient continuity. The generic data may be any common
family of numbers; the final corollaries use the actual Challenge eigenvalues.
-/

open Filter Asymptotics
open scoped Topology

set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace MF21Uniqueness

/-- A source-format expansion of order p for common data f, restricted to the
precise admissible range. Source index j is one-based. -/
def BulkExpansion (p : ℕ) (f : ℕ → ℕ → ℝ) (a : ℕ → ℝ → ℝ) : Prop :=
  ∃ D : ℝ, 0 < D ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ,
    1 ≤ j → j ≤ n → MF21Mesh.cutoff n ≤ j →
    |f n j - ∑ i ∈ Finset.range (p + 1),
      a i (MF21Mesh.grid n j) / MF21Mesh.denominator n ^ i| ≤
        D / MF21Mesh.denominator n ^ (p + 1)

theorem bulkExpansion_error_on_mesh
    (p : ℕ) (f : ℕ → ℕ → ℝ) (a : ℕ → ℝ → ℝ)
    (ha : BulkExpansion p f a) (x : ℝ) :
    (fun n ↦ f n (MF21Mesh.index x n) - ∑ i ∈ Finset.range (p + 1),
      a i (MF21Mesh.mesh x n) * ((MF21Mesh.denominator n)⁻¹) ^ i)
      =O[atTop] (fun n ↦ ((MF21Mesh.denominator n)⁻¹) ^ (p + 1)) := by
  obtain ⟨D, hD, N, ha⟩ := ha
  apply IsBigO.of_bound D
  filter_upwards [eventually_ge_atTop N, MF21Mesh.index_admissible x] with n hn hj
  have H := ha n hn (MF21Mesh.index x n) hj.1 hj.2.2 hj.2.1
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (pow_nonneg
    (inv_nonneg.mpr (MF21Mesh.denominator_pos n).le) (p + 1))]
  simpa only [MF21Mesh.mesh, div_eq_mul_inv, inv_pow] using H

/-- Any two continuous families satisfying the same order-p bulk expansion
coincide through order p everywhere on the closed interval, including 0 and pi. -/
theorem bulkExpansion_unique
    (p : ℕ) (f : ℕ → ℕ → ℝ) (a b : ℕ → ℝ → ℝ)
    (ha : ∀ k ≤ p, ContinuousOn (a k) (Set.Icc 0 Real.pi))
    (hb : ∀ k ≤ p, ContinuousOn (b k) (Set.Icc 0 Real.pi))
    (hea : BulkExpansion p f a) (heb : BulkExpansion p f b) :
    ∀ k ≤ p, ∀ x ∈ Set.Icc 0 Real.pi, a k x = b k x := by
  apply MF21Audit.top_expansion_unique_on_mesh (Set.Icc 0 Real.pi)
    MF21Mesh.mesh (fun n ↦ (MF21Mesh.denominator n)⁻¹) a b p
    MF21Mesh.mesh_tendsto
    (fun x _ ↦ Filter.Eventually.of_forall (MF21Mesh.mesh_mem x))
    MF21Mesh.inv_denominator_tendsto
    (Filter.Eventually.of_forall (fun n ↦ inv_ne_zero (ne_of_gt (MF21Mesh.denominator_pos n))))
    ha hb
  intro x hx
  have H := (bulkExpansion_error_on_mesh p f b heb x).sub
    (bulkExpansion_error_on_mesh p f a hea x)
  apply H.congr' _ (Filter.EventuallyEq.refl _ _)
  apply Filter.Eventually.of_forall
  intro n
  dsimp only
  simp only [sub_mul]
  rw [Finset.sum_sub_distrib]
  ring

/-- Total extension of the actual eigenvalue family to natural indices.
Only source indices 1 through n are ever used by BulkExpansion. -/
def eigenvalueData (m n j : ℕ) : ℝ :=
  if hj : j - 1 < n then MF21Challenge.eigenvalue m n ⟨j - 1, hj⟩ else 0

theorem bulkTopOrder_to_bulkExpansion (m : ℕ) (a : MF21Challenge.Coefficients)
    (ha : MF21Challenge.BulkTopOrder m a) :
    BulkExpansion (2 * m) (eigenvalueData m) a := by
  obtain ⟨D, hD, N, ha⟩ := ha
  refine ⟨D, hD, N, ?_⟩
  intro n hn j hj hn' hc
  have hjn : j - 1 < n := by omega
  have hsucc : j - 1 + 1 = j := Nat.sub_add_cancel hj
  have H := ha n hn ⟨j - 1, hjn⟩ (by simpa [MF21Challenge.cutoff,
    MF21Mesh.cutoff, MF21Mesh.denominator, hsucc] using hc)
  simpa [eigenvalueData, hjn, MF21Challenge.remainder, MF21Challenge.grid,
    MF21Mesh.grid, MF21Mesh.denominator, hsucc] using H

/-- The exact uniqueness claim for the two continuous coefficient families
in MF-21, including all endpoints. -/
theorem mf21_bulk_coefficients_unique (m : ℕ)
    (a b : MF21Challenge.Coefficients)
    (ha : MF21Challenge.ContinuousCoefficients m a)
    (hb : MF21Challenge.ContinuousCoefficients m b)
    (hea : MF21Challenge.BulkTopOrder m a)
    (heb : MF21Challenge.BulkTopOrder m b) :
    ∀ k ≤ 2 * m, ∀ x ∈ Set.Icc 0 Real.pi, a k x = b k x :=
  bulkExpansion_unique (2 * m) (eigenvalueData m) a b ha hb
    (bulkTopOrder_to_bulkExpansion m a hea) (bulkTopOrder_to_bulkExpansion m b heb)

/-- The uniform bound is in particular valid above the cutoff. -/
theorem uniformTopOrder_to_bulkTopOrder (m : ℕ) (a : MF21Challenge.Coefficients)
    (ha : MF21Challenge.UniformOrder m (2 * m) a) :
    MF21Challenge.BulkTopOrder m a := by
  obtain ⟨D, hD, N, ha⟩ := ha
  exact ⟨D, hD, N, fun n hn j _ ↦ ha n hn j⟩

/-- A hypothetical all-index expansion is forced to use the existing bulk
coefficients. This discharges the uniqueness objection without assuming the
hypothetical coefficients extend continuously beyond [0,pi]. -/
theorem mf21_uniform_coefficients_eq_bulk (m : ℕ)
    (a b : MF21Challenge.Coefficients)
    (ha : MF21Challenge.ContinuousCoefficients m a)
    (hb : MF21Challenge.ContinuousCoefficients m b)
    (hea : MF21Challenge.BulkTopOrder m a)
    (heb : MF21Challenge.UniformOrder m (2 * m) b) :
    ∀ k ≤ 2 * m, ∀ x ∈ Set.Icc 0 Real.pi, a k x = b k x :=
  mf21_bulk_coefficients_unique m a b ha hb hea
    (uniformTopOrder_to_bulkTopOrder m b heb)

/-- Every actual source grid point lies in the closed coefficient domain. -/
theorem challenge_grid_mem (n : ℕ) (j : Fin n) :
    MF21Challenge.grid n j ∈ Set.Icc 0 Real.pi := by
  have hj : (((j.val + 1 : ℕ) : ℝ)) ≤ (n : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt j.isLt
  have hd : 0 < (n : ℝ) + 2 := by positivity
  dsimp [MF21Challenge.grid]
  constructor
  · positivity
  · apply (div_le_iff₀ hd).mpr
    nlinarith [Real.pi_pos]

/-- Transfer a uniform estimate between families equal on the actual domain. -/
theorem uniformOrder_congr (m p : ℕ) (a b : MF21Challenge.Coefficients)
    (hab : ∀ k ≤ p, ∀ x ∈ Set.Icc 0 Real.pi, a k x = b k x)
    (hb : MF21Challenge.UniformOrder m p b) :
    MF21Challenge.UniformOrder m p a := by
  obtain ⟨D, hD, N, hb⟩ := hb
  refine ⟨D, hD, N, ?_⟩
  intro n hn j
  have hr : MF21Challenge.remainder m p n a j =
      MF21Challenge.remainder m p n b j := by
    unfold MF21Challenge.remainder
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [hab k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) _
      (challenge_grid_mem n j)]
  rw [hr]
  exact hb n hn j

/-- The original same-family target entails the stronger obstruction for every
continuous family. This is an implication, not a proof of its antecedent. -/
theorem universalObstruction_of_fullTarget
    (h : MF21Challenge.FullTarget) : MF21Challenge.UniversalObstruction := by
  intro m hm b hb hbu
  obtain ⟨a, ha, _, _, habulk, hno⟩ := h m hm
  exact hno (uniformOrder_congr m (2 * m) a b
    (mf21_uniform_coefficients_eq_bulk m a b ha hb habulk hbu) hbu)

end MF21Uniqueness

#print axioms MF21Uniqueness.bulkExpansion_unique
#print axioms MF21Uniqueness.mf21_bulk_coefficients_unique
#print axioms MF21Uniqueness.mf21_uniform_coefficients_eq_bulk

#print axioms MF21Uniqueness.universalObstruction_of_fullTarget
