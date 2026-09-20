import MF21.QuantizationTaylor
import MF21.LogSquaredMesh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Sharp transfer of phase errors to symbol errors. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace MF21Expansion

def step (n : ℕ) : ℝ := ((n : ℝ) + 2)⁻¹

theorem step_pos (n : ℕ) : 0 < step n := by unfold step; positivity

theorem step_tendsto : Tendsto step atTop (𝓝 0) := MF21Mesh.inv_denominator_tendsto

theorem grid_eq (n : ℕ) (j : Fin n) :
    MF21Challenge.grid n j = (j.val + 1 : ℕ) * Real.pi * step n := by
  simp only [MF21Challenge.grid, step, div_eq_mul_inv]

theorem grid_mem (n : ℕ) (j : Fin n) : MF21Challenge.grid n j ∈ Icc 0 Real.pi := by
  have hd : 0 < (n : ℝ) + 2 := by positivity
  have hj : (j.val + 1 : ℝ) ≤ n := by exact_mod_cast j.isLt
  constructor
  · unfold MF21Challenge.grid
    positivity
  · rw [MF21Challenge.grid, div_le_iff₀ hd]
    push_cast
    nlinarith [Real.pi_pos]

/-- The actual inverse angle lies inside the symbol interval at every source grid point. -/
theorem model_grid_angle_mem (m : ℕ) (hm : 1 ≤ m) (model : MF21Quantization.Model m)
    (n : ℕ) (j : Fin n) (hh : step n ≤ model.H) :
    model.Y (MF21Challenge.grid n j, step n) ∈ Ioo 0 Real.pi := by
  have hp : (MF21Challenge.grid n j, step n) ∈ Icc 0 Real.pi ×ˢ Icc 0 model.H :=
    ⟨grid_mem n j, (step_pos n).le, hh⟩
  constructor
  · apply model.above _ hp 0 ⟨le_rfl, Real.pi_pos.le⟩
    have hη : 0 ≤ model.eta 0 := by
      rw [model.eta_zero]
      have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
      positivity
    have hs : 0 < MF21Challenge.grid n j := by unfold MF21Challenge.grid; positivity
    nlinarith [mul_nonneg (step_pos n).le hη]
  · apply model.below _ hp Real.pi ⟨Real.pi_pos.le, le_rfl⟩
    rw [model.eta_pi, MF21Challenge.grid, step]
    have hd : 0 < (n : ℝ) + 2 := by positivity
    apply (div_lt_iff₀ hd).mpr
    have hj : (j.val + 1 : ℝ) ≤ n := by exact_mod_cast j.isLt
    have hid : ((n : ℝ) + 2)⁻¹ * ((n : ℝ) + 2) = 1 := inv_mul_cancel₀ (ne_of_gt hd)
    push_cast
    nlinarith [Real.pi_pos, mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hj)]

theorem sin_base_bound (theta : ℝ) (ht : 0 ≤ theta) : |2 * Real.sin (theta / 2)| ≤ theta := by
  calc
    _ = 2 * |Real.sin (theta / 2)| := by rw [abs_mul]; norm_num
    _ ≤ 2 * |theta / 2| := mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = theta := by rw [abs_of_nonneg (by positivity)]; ring

theorem sin_base_lipschitz (theta y : ℝ) :
    |2 * Real.sin (theta / 2) - 2 * Real.sin (y / 2)| ≤ |theta - y| := by
  calc
    _ = 2 * |Real.sin (theta / 2) - Real.sin (y / 2)| := by rw [← mul_sub, abs_mul]; norm_num
    _ ≤ 2 * |theta / 2 - y / 2| := mul_le_mul_of_nonneg_left (Real.abs_sin_sub_sin_le _ _) (by norm_num)
    _ = |theta - y| := by rw [← sub_div, abs_div]; norm_num; ring

/-- The symbol's vanishing order supplies the sharp power factor in its error estimate. -/
theorem symbol_power_lipschitz (m : ℕ) (theta y : ℝ) (ht : 0 ≤ theta) (hy : 0 ≤ y) :
    |MF21Challenge.symbol m theta - MF21Challenge.symbol m y| ≤
      (2 * m : ℝ) * max theta y ^ (2 * m - 1) * |theta - y| := by
  have hb : max |2 * Real.sin (theta / 2)| |2 * Real.sin (y / 2)| ≤ max theta y :=
    max_le_max (sin_base_bound theta ht) (sin_base_bound y hy)
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ max |2 * Real.sin (theta / 2)|
    |2 * Real.sin (y / 2)|) hb (2 * m - 1)
  have h := abs_pow_sub_pow_le (2 * Real.sin (theta / 2)) (2 * Real.sin (y / 2)) (2 * m)
  change |MF21Challenge.symbol m theta - MF21Challenge.symbol m y| ≤ _ at h
  have hprod := mul_le_mul (mul_le_mul_of_nonneg_right (sin_base_lipschitz theta y)
    (Nat.cast_nonneg (2 * m))) hpow (by positivity) (by positivity)
  exact h.trans (hprod.trans_eq (by push_cast; ring))


/-- Exponentially small angle error gains the full h^(2m) factor near zero. -/
theorem symbol_error_from_angle (m : ℕ) (hm : 1 ≤ m)
    (theta y j h A C c : ℝ) (ht : 0 ≤ theta) (hy : 0 ≤ y)
    (hj : 1 ≤ j) (hh : 0 ≤ h) (hA : 0 ≤ A) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hangle : |theta - y| ≤ C * h * Real.exp (-c * j))
    (hscale : theta ≤ A * j * h) :
    |MF21Challenge.symbol m theta - MF21Challenge.symbol m y| ≤
      ((2 * m : ℝ) * C * (A + C) ^ (2 * m - 1)) *
        (j ^ (2 * m - 1) * Real.exp (-c * j)) * h ^ (2 * m) := by
  have hex : Real.exp (-c * j) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hd : |theta - y| ≤ C * h :=
    hangle.trans ((mul_le_mul_of_nonneg_left hex (mul_nonneg hC hh)).trans_eq (by ring))
  have hym : y ≤ (A + C) * j * h := by
    have hdiff := le_abs_self (y - theta)
    rw [abs_sub_comm] at hdiff
    nlinarith [mul_nonneg hC (mul_nonneg (sub_nonneg.mpr hj) hh)]
  have htm : theta ≤ (A + C) * j * h := by
    nlinarith [mul_nonneg hC (mul_nonneg (by linarith : 0 ≤ j) hh)]
  have hmax := max_le htm hym
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ max theta y) hmax (2 * m - 1)
  have hg := symbol_power_lipschitz m theta y ht hy
  have hprod := mul_le_mul
    (mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ (2 * m : ℝ))) hangle
    (abs_nonneg _) (by positivity)
  apply hg.trans (hprod.trans_eq ?_)
  rw [show h ^ (2 * m) = h ^ (2 * m - 1) * h by
    rw [← pow_succ]; congr 1; omega]
  simp only [mul_pow]
  ring

/-- The remaining spectral input to the expansion construction: actual sorted
eigenangles with exponential phase error and their linear small-angle bound. -/
def TailAngleApproximation (m : ℕ) (model : MF21Quantization.Model m) : Prop :=
  ∃ J N : ℕ, ∃ C c A : ℝ, 0 < C ∧ 0 < c ∧ 0 < A ∧
    ∀ n : ℕ, N ≤ n → ∀ j : Fin n, J ≤ j.val + 1 →
      ∃ theta : ℝ, theta ∈ Ioo 0 Real.pi ∧
        MF21Challenge.eigenvalue m n j = MF21Challenge.symbol m theta ∧
        |theta - model.Y (MF21Challenge.grid n j, step n)| ≤
          C * step n * Real.exp (-c * (j.val + 1 : ℕ)) ∧
        theta ≤ A * (j.val + 1 : ℕ) * step n

def TailSymbolApproximation (m : ℕ) (model : MF21Quantization.Model m) : Prop :=
  ∃ J N : ℕ, ∃ B c : ℝ, 0 < B ∧ 0 < c ∧
    ∀ n : ℕ, N ≤ n → ∀ j : Fin n, J ≤ j.val + 1 →
      |MF21Challenge.eigenvalue m n j - model.F (MF21Challenge.grid n j, step n)| ≤
        B * (((j.val + 1 : ℕ) : ℝ) ^ (2 * m - 1) * Real.exp (-c * (j.val + 1 : ℕ))) *
          step n ^ (2 * m)

theorem tailSymbol_of_tailAngle (m : ℕ) (hm : 1 ≤ m) (model : MF21Quantization.Model m)
    (htail : TailAngleApproximation m model) : TailSymbolApproximation m model := by
  obtain ⟨J, N, C, c, A, hC, hc, hA, ht⟩ := htail
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (step_tendsto.eventually_lt_const model.Hpos)
  refine ⟨J, max N N₁, (2 * m : ℝ) * C * (A + C) ^ (2 * m - 1), c,
    ?_, hc, ?_⟩
  · have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    positivity
  · intro n hn j hj
    obtain ⟨theta, htheta, he, herr, hscale⟩ := ht n ((le_max_left _ _).trans hn) j hj
    have hy := model_grid_angle_mem m hm model n j
      (hN₁ n ((le_max_right _ _).trans hn)).le
    rw [he]
    exact symbol_error_from_angle m hm theta _ (j.val + 1 : ℕ) (step n) A C c
      htheta.1.le hy.1.le (by exact_mod_cast (show 1 ≤ j.val + 1 by omega))
      (step_pos n).le hA.le hC.le hc.le herr hscale
end MF21Expansion
#print axioms MF21Expansion.model_grid_angle_mem
#print axioms MF21Expansion.symbol_power_lipschitz

#print axioms MF21Expansion.tailSymbol_of_tailAngle
