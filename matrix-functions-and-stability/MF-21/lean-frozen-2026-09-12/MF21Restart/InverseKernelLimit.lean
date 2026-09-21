import MF21Restart.InverseKernelGrid
import Mathlib.Algebra.Order.Floor.Semiring

/-! The actual clamped-ceiling step kernel converges uniformly on the
whole closed square. Prior lock: INVERSE_KERNEL_LIMIT_STATEMENTS.md. -/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

def kernelCellIndex (n : ℕ) (hn : 0 < n) (x : ℝ) : Fin n :=
  ⟨min (Nat.ceil ((n : ℝ) * x) - 1) (n - 1),
    (min_le_right _ _).trans_lt (by omega)⟩

theorem kernelCellIndex_val (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    (kernelCellIndex n hn x).val = Nat.ceil ((n : ℝ) * x) - 1 := by
  have hc : Nat.ceil ((n : ℝ) * x) ≤ n := Nat.ceil_le.mpr (by
    have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [hx.2])
  exact min_eq_left (Nat.sub_le_sub_right hc 1)

theorem kernelGridPoint_cell_bounds (n : ℕ) (hn : 0 < n)
    (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    x ≤ kernelGridPoint n (kernelCellIndex n hn x) ∧
      kernelGridPoint n (kernelCellIndex n hn x) ≤ x + 1 / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
  have hnx : 0 ≤ (n : ℝ) * x := mul_nonneg hnpos.le hx.1
  unfold kernelGridPoint
  rw [kernelCellIndex_val n hn x hx]
  by_cases hx0 : x = 0
  · subst x
    simp only [mul_zero, Nat.ceil_zero, Nat.zero_sub, zero_add, Nat.cast_one]
    exact ⟨by positivity, le_rfl⟩
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    have hc1 : 1 ≤ Nat.ceil ((n : ℝ) * x) :=
      Nat.one_le_ceil_iff.mpr (mul_pos hnpos hxpos)
    rw [Nat.sub_add_cancel hc1]
    constructor
    · apply (le_div_iff₀ hnpos).mpr
      simpa only [mul_comm] using Nat.le_ceil ((n : ℝ) * x)
    · apply (div_le_iff₀ hnpos).mpr
      have he : (x + 1 / (n : ℝ)) * n = (n : ℝ) * x + 1 := by
        field_simp
        <;> ring
      rw [he]
      exact (Nat.ceil_lt_add_one hnx).le

def inverseStepKernel (m n : ℕ) (hn : 0 < n) (x y : ℝ) : ℝ :=
  (1 / (n : ℝ)) ^ (2 * m - 1) *
    (toeplitz m n)⁻¹ (kernelCellIndex n hn x) (kernelCellIndex n hn y)

theorem toeplitz_inverse_kernel_uniform (m : ℕ) (hm : 1 ≤ m) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 4 ≤ N ∧
      ∀ (n : ℕ) (hn : 0 < n), N ≤ n → ∀ x y : ℝ,
        x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 →
          |inverseStepKernel m n hn x y - inverseKernel m x y| ≤ ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨N₁, hN₁, hgrid⟩ := toeplitz_inverse_grid_uniform m hm (ε / 2) hhalf
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (inverseKernel_uniformContinuousOn m) (ε / 2) hhalf
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (1 / δ)
  refine ⟨max N₁ N₂, hN₁.trans (le_max_left _ _), ?_⟩
  intro n hn hnN x y hx hy
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hnN
  have hn₂ : N₂ ≤ n := (le_max_right _ _).trans hnN
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsmall : 1 / (n : ℝ) < δ := by
    have ht : 1 / δ < (n : ℝ) := hN₂.trans_le (by exact_mod_cast hn₂)
    have hm := (div_lt_iff₀ hδ).mp ht
    apply (div_lt_iff₀ hnpos).mpr
    simpa only [mul_comm] using hm
  let i := kernelCellIndex n hn x
  let j := kernelCellIndex n hn y
  have hix := kernelGridPoint_cell_bounds n hn x hx
  have hjy := kernelGridPoint_cell_bounds n hn y hy
  have hd : dist (kernelGridPoint n i, kernelGridPoint n j) (x, y) ≤ 1 / (n : ℝ) := by
    rw [Prod.dist_eq]
    apply max_le
    · change dist (kernelGridPoint n i) x ≤ 1 / (n : ℝ)
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hix.1)]
      linarith only [hix.2]
    · change dist (kernelGridPoint n j) y ≤ 1 / (n : ℝ)
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hjy.1)]
      linarith only [hjy.2]
  have hb := hclose (kernelGridPoint n i, kernelGridPoint n j)
    (kernelUnitSquare_mem _ _ (kernelGridPoint_mem_unit n i) (kernelGridPoint_mem_unit n j))
    (x, y) (kernelUnitSquare_mem x y hx hy) (hd.trans_lt hsmall)
  change dist (inverseKernel m (kernelGridPoint n i) (kernelGridPoint n j))
    (inverseKernel m x y) < ε / 2 at hb
  rw [Real.dist_eq] at hb
  have he := hgrid n hn₁ i j
  change |inverseStepKernel m n hn x y -
    inverseKernel m (kernelGridPoint n i) (kernelGridPoint n j)| ≤ ε / 2 at he
  calc
    |inverseStepKernel m n hn x y - inverseKernel m x y| ≤
        |inverseStepKernel m n hn x y - inverseKernel m (kernelGridPoint n i) (kernelGridPoint n j)| +
        |inverseKernel m (kernelGridPoint n i) (kernelGridPoint n j) - inverseKernel m x y| :=
      abs_sub_le _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add he hb.le
    _ = ε := by ring

#print axioms kernelCellIndex_val
#print axioms kernelGridPoint_cell_bounds
#print axioms toeplitz_inverse_kernel_uniform

end MF21Restart
