import MF21Restart.InverseKernelContinuity

/-! Uniform convergence on every actual one-based grid point; the reversal
shift is retained. Prior lock: INVERSE_KERNEL_GRID_STATEMENTS.md. -/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

theorem kernelUnitSquare_mem (x y : ℝ) (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    (x, y) ∈ kernelUnitSquare := by
  exact ⟨⟨hx.1, hy.1⟩, ⟨hx.2, hy.2⟩⟩

theorem kernelGridPoint_rev (n : ℕ) (i : Fin n) :
    kernelGridPoint n i.rev = 1 - kernelGridPoint n i + 1 / n := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by have := i.isLt; omega)
  have hi : i.val + 1 ≤ n := by omega
  unfold kernelGridPoint
  rw [Fin.val_rev, Nat.cast_add, Nat.cast_one, Nat.cast_sub hi]
  field_simp
  <;> ring

theorem toeplitz_inverse_grid_uniform (m : ℕ) (hm : 1 ≤ m) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 4 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ i j : Fin n,
        |(1 / (n : ℝ)) ^ (2 * m - 1) * (toeplitz m n)⁻¹ i j -
          inverseKernel m (kernelGridPoint n i) (kernelGridPoint n j)| ≤ ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨N₁, hN₁, htop⟩ := toeplitz_inverse_grid_top_uniform m hm (ε / 2) hhalf
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (inverseKernel_uniformContinuousOn m) (ε / 2) hhalf
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (1 / δ)
  refine ⟨max N₁ N₂, hN₁.trans (le_max_left _ _), ?_⟩
  intro n hn i j
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : N₂ ≤ n := (le_max_right _ _).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := i.isLt; omega)
  have hh : 0 ≤ 1 / (n : ℝ) := by positivity
  have hsmall : 1 / (n : ℝ) < δ := by
    have ht : 1 / δ < (n : ℝ) := hN₂.trans_le (by exact_mod_cast hn₂)
    have hm := (div_lt_iff₀ hδ).mp ht
    apply (div_lt_iff₀ hnpos).mpr
    simpa only [mul_comm] using hm
  by_cases hxy : 1 ≤ kernelGridPoint n i + kernelGridPoint n j
  · have he := htop n hn₁ i j hxy
    rw [← inverseKernel_eq_top m (kernelGridPoint n i) (kernelGridPoint n j) hxy] at he
    exact he.trans (by linarith only [hε])
  · have hrev : 1 ≤ kernelGridPoint n i.rev + kernelGridPoint n j.rev := by
      rw [kernelGridPoint_rev, kernelGridPoint_rev]
      linarith only [not_le.mp hxy, hh]
    have he := htop n hn₁ i.rev j.rev hrev
    rw [toeplitz_inverse_rev,
      ← inverseKernel_eq_top m (kernelGridPoint n i.rev) (kernelGridPoint n j.rev) hrev] at he
    have hx := kernelGridPoint_mem_unit n i
    have hy := kernelGridPoint_mem_unit n j
    have hxr : 1 - kernelGridPoint n i ∈ Set.Icc 0 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hyr : 1 - kernelGridPoint n j ∈ Set.Icc 0 1 := ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have hdist : dist (kernelGridPoint n i.rev, kernelGridPoint n j.rev)
        (1 - kernelGridPoint n i, 1 - kernelGridPoint n j) < δ := by
      rw [Prod.dist_eq]
      apply max_lt_iff.mpr
      constructor
      · change dist (kernelGridPoint n i.rev) (1 - kernelGridPoint n i) < δ
        rw [kernelGridPoint_rev, Real.dist_eq,
          show 1 - kernelGridPoint n i + 1 / (n : ℝ) - (1 - kernelGridPoint n i) =
            1 / n by ring, abs_of_nonneg hh]
        exact hsmall
      · change dist (kernelGridPoint n j.rev) (1 - kernelGridPoint n j) < δ
        rw [kernelGridPoint_rev, Real.dist_eq,
          show 1 - kernelGridPoint n j + 1 / (n : ℝ) - (1 - kernelGridPoint n j) =
            1 / n by ring, abs_of_nonneg hh]
        exact hsmall
    have hb := hclose (kernelGridPoint n i.rev, kernelGridPoint n j.rev)
      (kernelUnitSquare_mem _ _ (kernelGridPoint_mem_unit n i.rev) (kernelGridPoint_mem_unit n j.rev))
      (1 - kernelGridPoint n i, 1 - kernelGridPoint n j) (kernelUnitSquare_mem _ _ hxr hyr) hdist
    change dist (inverseKernel m (kernelGridPoint n i.rev) (kernelGridPoint n j.rev))
      (inverseKernel m (1 - kernelGridPoint n i) (1 - kernelGridPoint n j)) < ε / 2 at hb
    rw [Real.dist_eq, inverseKernel_reflection] at hb
    calc
      |(1 / (n : ℝ)) ^ (2 * m - 1) * (toeplitz m n)⁻¹ i j -
          inverseKernel m (kernelGridPoint n i) (kernelGridPoint n j)| ≤
          |(1 / (n : ℝ)) ^ (2 * m - 1) * (toeplitz m n)⁻¹ i j -
            inverseKernel m (kernelGridPoint n i.rev) (kernelGridPoint n j.rev)| +
          |inverseKernel m (kernelGridPoint n i.rev) (kernelGridPoint n j.rev) -
            inverseKernel m (kernelGridPoint n i) (kernelGridPoint n j)| := abs_sub_le _ _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add he hb.le
      _ = ε := by ring

#print axioms kernelUnitSquare_mem
#print axioms kernelGridPoint_rev
#print axioms toeplitz_inverse_grid_uniform

end MF21Restart
