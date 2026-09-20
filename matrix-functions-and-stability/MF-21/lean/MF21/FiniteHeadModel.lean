import MF21.SymbolTransfer
import MF21.SpectralBounds

/-! Uniform control of finitely many initial eigenvalues and model values. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace MF21Expansion

theorem symbol_abs_le_power (m : ℕ) (theta : ℝ) (ht : 0 ≤ theta) :
    |MF21Challenge.symbol m theta| ≤ theta ^ (2 * m) := by
  rw [MF21Challenge.symbol, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (sin_base_bound theta ht) _

theorem eigenvalue_abs_upper_head (m n J : ℕ) (j : Fin n) (hj : j.val + 1 ≤ J) :
    |MF21Challenge.eigenvalue m n j| ≤
      (3 * Real.pi * ((J : ℝ) + 2 * m)) ^ (2 * m) * step n ^ (2 * m) := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by have := j.isLt; omega)
  have hnp : 0 < (n : ℝ) := by linarith
  have hd : 0 < (n : ℝ) + 2 := by positivity
  have hjr : (j.val : ℝ) + 1 ≤ J := by exact_mod_cast hj
  have hnon : 0 ≤ MF21Challenge.eigenvalue m n j :=
    (by positivity : 0 ≤ (4 * ((j.val + 1) / 2 : ℕ) / ((n : ℝ) + 2 * m)) ^ (2 * m)).trans
      (MF21Circulant.toeplitz_eigenvalue_lower m n j)
  rw [abs_of_nonneg hnon, ← mul_pow]
  apply (MF21Circulant.toeplitz_eigenvalue_upper m n j).trans
  apply pow_le_pow_left₀ (by positivity)
  calc
    Real.pi * ((j.val : ℝ) + 1 + 2 * m) / n ≤ Real.pi * ((J : ℝ) + 2 * m) / n := by
      gcongr
    _ ≤ 3 * Real.pi * ((J : ℝ) + 2 * m) * step n := by
      rw [step, ← div_eq_mul_inv, div_le_div_iff₀ hnp hd]
      nlinarith [mul_nonneg (show 0 ≤ Real.pi * ((J : ℝ) + 2 * m) by positivity)
        (show 0 ≤ 3 * (n : ℝ) - ((n : ℝ) + 2) by linarith)]

theorem model_abs_upper_head (m : ℕ) (hm : 1 ≤ m) (model : MF21Quantization.Model m)
    (n J : ℕ) (j : Fin n) (hj : j.val + 1 ≤ J) (hh : step n ≤ model.H) :
    |model.F (MF21Challenge.grid n j, step n)| ≤
      (2 * ((J : ℝ) * Real.pi + model.eta 0)) ^ (2 * m) * step n ^ (2 * m) := by
  have hp : (MF21Challenge.grid n j, step n) ∈ Icc 0 Real.pi ×ˢ Icc 0 model.H :=
    ⟨grid_mem n j, (step_pos n).le, hh⟩
  have hy := model_grid_angle_mem m hm model n j hh
  have hη : 0 ≤ model.eta 0 := by
    rw [model.eta_zero]
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    positivity
  have hd := model.inverse_distance _ hp 0 ⟨le_rfl, Real.pi_pos.le⟩
  rw [sub_zero, zero_sub, sub_neg_eq_add, abs_of_nonneg hy.1.le,
    abs_of_nonneg (add_nonneg (grid_mem n j).1 (mul_nonneg (step_pos n).le hη))] at hd
  have hjr : ((j.val + 1 : ℕ) : ℝ) ≤ J := by exact_mod_cast hj
  have hb : model.Y (MF21Challenge.grid n j, step n) ≤
      2 * ((J : ℝ) * Real.pi + model.eta 0) * step n := by
    rw [grid_eq] at hd ⊢
    nlinarith [mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hjr Real.pi_pos.le) (step_pos n).le]
  change |MF21Challenge.symbol m (model.Y _)| ≤ _
  apply (symbol_abs_le_power m _ hy.1.le).trans
  rw [← mul_pow]
  exact pow_le_pow_left₀ hy.1.le hb _

theorem finite_head_model_error (m : ℕ) (hm : 1 ≤ m) (model : MF21Quantization.Model m)
    (J : ℕ) : ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, ∀ j : Fin n,
      j.val + 1 ≤ J → step n ≤ model.H →
      |MF21Challenge.eigenvalue m n j - model.F (MF21Challenge.grid n j, step n)| ≤
        K * step n ^ (2 * m) := by
  let K := (3 * Real.pi * ((J : ℝ) + 2 * m)) ^ (2 * m) +
    (2 * ((J : ℝ) * Real.pi + model.eta 0)) ^ (2 * m) + 1
  have hη : 0 ≤ model.eta 0 := by
    rw [model.eta_zero]
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    positivity
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro n j hj hh
  have heig := eigenvalue_abs_upper_head m n J j hj
  have hF := model_abs_upper_head m hm model n J j hj hh
  have ht := abs_sub_le (MF21Challenge.eigenvalue m n j) 0 (model.F (MF21Challenge.grid n j, step n))
  simp only [sub_zero, zero_sub, abs_neg] at ht
  dsimp [K]
  nlinarith [pow_nonneg (step_pos n).le (2 * m)]

end MF21Expansion
#print axioms MF21Expansion.finite_head_model_error
