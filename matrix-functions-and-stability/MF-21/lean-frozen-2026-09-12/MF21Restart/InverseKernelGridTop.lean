import MF21Restart.KernelShiftedSum
import MF21Restart.ScaledInverseSum

/-! Uniform convergence of the actual inverse on one-based grid points in
the upper half of the square. Prior lock: INVERSE_KERNEL_GRID_TOP_STATEMENTS.md. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

def kernelGridPoint (n : ℕ) (i : Fin n) : ℝ := ((i.val + 1 : ℕ) : ℝ) / n

def inverseKernelTop (m : ℕ) (x y : ℝ) : ℝ :=
  ∫ t in max x y..1, finiteKernelIntegrand m 0 x y t

theorem kernelGridPoint_mem_unit (n : ℕ) (i : Fin n) :
    kernelGridPoint n i ∈ Set.Icc 0 1 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := i.isLt; omega)
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hn.le
  · exact (div_le_one hn).mpr (by exact_mod_cast (show i.val + 1 ≤ n by omega))

theorem kernelGridPoint_max (n : ℕ) (i j : Fin n) :
    max (kernelGridPoint n i) (kernelGridPoint n j) =
      ((max i.val j.val + 1 : ℕ) : ℝ) / n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  by_cases hij : i.val ≤ j.val
  · have hxy : kernelGridPoint n i ≤ kernelGridPoint n j :=
      div_le_div_of_nonneg_right (by exact_mod_cast (Nat.add_le_add_right hij 1)) hn
    rw [max_eq_right hxy, max_eq_right hij]
    rfl
  · have hji : j.val ≤ i.val := by omega
    have hyx : kernelGridPoint n j ≤ kernelGridPoint n i :=
      div_le_div_of_nonneg_right (by exact_mod_cast (Nat.add_le_add_right hji 1)) hn
    rw [max_eq_left hyx, max_eq_left hji]
    rfl

private theorem guarded_fin_sum_eq_Ico (n : ℕ) (i j : Fin n) (f : ℕ → ℝ) :
    (∑ k : Fin n, if i.val ≤ k.val ∧ j.val ≤ k.val then f k.val else 0) =
      ∑ k ∈ Finset.Ico (max i.val j.val) n, f k := by
  classical
  have hfilter : (∑ k : Fin n, if i.val ≤ k.val ∧ j.val ≤ k.val then f k.val else 0) =
      ∑ k ∈ (Finset.univ : Finset (Fin n)).filter
        (fun k => i.val ≤ k.val ∧ j.val ≤ k.val), f k.val := by
    rw [Finset.sum_filter]
  rw [hfilter]
  apply Finset.sum_bij (fun k _ => k.val)
  · intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    exact Finset.mem_Ico.mpr ⟨max_le hk'.1 hk'.2, k.isLt⟩
  · intro k hk ell hell h
    exact Fin.ext h
  · intro k hk
    have hk' := Finset.mem_Ico.mp hk
    refine ⟨⟨k, hk'.2⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, max_le_iff.mp hk'.1⟩
  · intro k hk
    rfl

theorem scaled_toeplitz_inverse_eq_grid_sum (m n : ℕ) (hm : 1 ≤ m) (i j : Fin n) :
    (1 / (n : ℝ)) ^ (2 * m - 1) * (toeplitz m n)⁻¹ i j =
      (1 / (n : ℝ)) * ∑ k ∈ Finset.Ico (max i.val j.val) n,
        finiteKernelIntegrand m (1 / n) (kernelGridPoint n i) (kernelGridPoint n j)
          (((k + 1 : ℕ) : ℝ) / n) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := i.isLt; omega)
  have hh : (1 / (n : ℝ)) ≠ 0 := ne_of_gt (by positivity)
  have hg (k : Fin n) : (1 / (n : ℝ)) * ((k.val : ℝ) + 1) = kernelGridPoint n k := by
    unfold kernelGridPoint
    push_cast
    ring
  rw [scaled_toeplitz_inverse_eq_sum m n hm (1 / n) hh i j]
  simp_rw [hg]
  congr 1
  exact guarded_fin_sum_eq_Ico n i j (fun k =>
    finiteKernelIntegrand m (1 / n) (kernelGridPoint n i) (kernelGridPoint n j)
      (((k + 1 : ℕ) : ℝ) / n))

theorem toeplitz_inverse_grid_top_uniform (m : ℕ) (hm : 1 ≤ m) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 4 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ i j : Fin n,
        1 ≤ kernelGridPoint n i + kernelGridPoint n j →
          |(1 / (n : ℝ)) ^ (2 * m - 1) * (toeplitz m n)⁻¹ i j -
            inverseKernelTop m (kernelGridPoint n i) (kernelGridPoint n j)| ≤ ε := by
  intro ε hε
  obtain ⟨N, hN, hsum⟩ := finiteKernelIntegrand_uniform_shifted_sum m ε hε
  refine ⟨N, hN, ?_⟩
  intro n hn i j htop
  have hn4 : 4 ≤ n := hN.trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn4r : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hstep : 1 / (n : ℝ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hn4r
  have hx := kernelGridPoint_mem_unit n i
  have hy := kernelGridPoint_mem_unit n j
  let a : ℕ := max i.val j.val
  let b : ℝ := max (kernelGridPoint n i) (kernelGridPoint n j)
  have ha : a < n := max_lt i.isLt j.isLt
  have hbg : b = (a : ℝ) / n + 1 / n := by
    dsimp only [b]
    rw [kernelGridPoint_max]
    dsimp only [a]
    push_cast
    ring
  have hbhalf : (1 / 2 : ℝ) ≤ b := by
    have hi := le_max_left (kernelGridPoint n i) (kernelGridPoint n j)
    have hj := le_max_right (kernelGridPoint n i) (kernelGridPoint n j)
    change kernelGridPoint n i ≤ b at hi
    change kernelGridPoint n j ≤ b at hj
    linarith only [hi, hj, htop]
  have hstart : (1 / 4 : ℝ) ≤ (a : ℝ) / n := by linarith only [hbg, hbhalf, hstep]
  have hb : b ∈ Set.Icc ((a : ℝ) / n) 1 := by
    constructor
    · rw [hbg]
      have hp : 0 ≤ 1 / (n : ℝ) := by positivity
      linarith only [hp]
    · exact max_le hx.2 hy.2
  have hshift : b - (a : ℝ) / n ≤ 1 / n := by rw [hbg]; linarith
  have he := hsum n hn (kernelGridPoint n i) (kernelGridPoint n j)
    hx hy a ha.le hstart b hb hshift
  rw [scaled_toeplitz_inverse_eq_grid_sum m n hm i j]
  exact he

#print axioms kernelGridPoint_mem_unit
#print axioms kernelGridPoint_max
#print axioms scaled_toeplitz_inverse_eq_grid_sum
#print axioms toeplitz_inverse_grid_top_uniform

end MF21Restart
