import MF21Restart.InverseKernelGrid
import MF21Restart.ActualKernelDiagonal
import MF21Restart.GridAverage
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecificLimits.Basic

/-! Actual scaled inverse trace limits, including the n+2 normalization
in (29). Prior lock: ACTUAL_TRACE_LIMIT_STATEMENTS.md. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology

namespace MF21Restart

theorem toeplitz_inverse_trace_tendsto_n (m : ℕ) (hm : 1 ≤ m) :
    Filter.Tendsto (fun n : ℕ => (1 / (n : ℝ)) ^ (2 * m) * Matrix.trace (toeplitz m n)⁻¹)
      Filter.atTop (𝓝 (kernelTraceConstant m)) := by
  have hc : Continuous (fun x : ℝ => inverseKernel m x x) :=
    (continuous_inverseKernel m).comp (continuous_id.prodMk continuous_id)
  have havg := continuous_grid_average_tendsto (fun x => inverseKernel m x x) hc.continuousOn
  rw [inverseKernel_diagonal_integral m hm] at havg
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨N₁, hN₁, hgrid⟩ := toeplitz_inverse_grid_uniform m hm (ε / 2) hhalf
  obtain ⟨N₂, havg⟩ := Metric.tendsto_atTop.mp havg (ε / 2) hhalf
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : N₂ ≤ n := (le_max_right _ _).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
  have hh : 0 ≤ 1 / (n : ℝ) := by positivity
  have hp : (2 * m - 1) + 1 = 2 * m := by omega
  have hscale : (1 / (n : ℝ)) ^ (2 * m) * Matrix.trace (toeplitz m n)⁻¹ =
      (1 / (n : ℝ)) * ∑ i : Fin n,
        (1 / (n : ℝ)) ^ (2 * m - 1) * (toeplitz m n)⁻¹ i i := by
    rw [← Finset.mul_sum, ← mul_assoc, mul_comm (1 / (n : ℝ)), ← pow_succ, hp]
    rfl
  have he : |(1 / (n : ℝ)) ^ (2 * m) * Matrix.trace (toeplitz m n)⁻¹ -
      (1 / (n : ℝ)) * ∑ i : Fin n, inverseKernel m (kernelGridPoint n i) (kernelGridPoint n i)| ≤
        ε / 2 := by
    rw [hscale, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hh]
    calc
      (1 / (n : ℝ)) * |∑ i : Fin n,
          ((1 / (n : ℝ)) ^ (2 * m - 1) * (toeplitz m n)⁻¹ i i -
            inverseKernel m (kernelGridPoint n i) (kernelGridPoint n i))| ≤
          (1 / (n : ℝ)) * ∑ i : Fin n,
            |(1 / (n : ℝ)) ^ (2 * m - 1) * (toeplitz m n)⁻¹ i i -
              inverseKernel m (kernelGridPoint n i) (kernelGridPoint n i)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hh
      _ ≤ (1 / (n : ℝ)) * ∑ _i : Fin n, ε / 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hgrid n hn₁ i i)) hh
      _ = ε / 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
  have ha := havg n hn₂
  rw [Real.dist_eq] at ha ⊢
  exact (abs_sub_le _
    ((1 / (n : ℝ)) * ∑ i : Fin n, inverseKernel m (kernelGridPoint n i) (kernelGridPoint n i))
    _).trans_lt (by linarith only [he, ha])

theorem toeplitz_inverse_trace_tendsto_mesh (m : ℕ) (hm : 1 ≤ m) :
    Filter.Tendsto (fun n : ℕ => (1 / (n + 2 : ℝ)) ^ (2 * m) * Matrix.trace (toeplitz m n)⁻¹)
      Filter.atTop (𝓝 (kernelTraceConstant m)) := by
  have hp := ((tendsto_natCast_div_add_atTop (2 : ℝ)).pow (2 * m)).mul
    (toeplitz_inverse_trace_tendsto_n m hm)
  simp only [one_pow, one_mul] at hp
  apply hp.congr'
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hden : (n + 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have he : ((n : ℝ) / (n + 2)) * (1 / n) = 1 / (n + 2) := by field_simp
  rw [← mul_assoc, ← mul_pow, he]

#print axioms toeplitz_inverse_trace_tendsto_n
#print axioms toeplitz_inverse_trace_tendsto_mesh

end MF21Restart
