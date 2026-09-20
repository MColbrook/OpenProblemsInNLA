import MF21.LogSquaredMesh
import MF21.Definitions
import Mathlib.Analysis.Complex.Exponential

/-! Polynomial exponential decay and the exact logarithm-squared index cutoff. -/
noncomputable section
open Filter
open scoped Topology
namespace MF21Expansion

theorem exponential_power_bound (r : ℕ) (a x : ℝ) (ha : 0 < a) (hx : 0 ≤ x) :
    x ^ r * Real.exp (-a * x) ≤ (r.factorial : ℝ) / a ^ r := by
  have hb := Real.pow_div_factorial_le_exp (a * x) (mul_nonneg ha.le hx) r
  have hf : 0 < (r.factorial : ℝ) := by positivity
  have hb' := (div_le_iff₀ hf).mp hb
  have hm := mul_le_mul_of_nonneg_right hb' (Real.exp_pos (-a * x)).le
  have he : (Real.exp (a * x) * (r.factorial : ℝ)) * Real.exp (-a * x) = r.factorial := by
    rw [mul_right_comm, ← Real.exp_add]
    simp
  rw [he] at hm
  apply (le_div_iff₀ (pow_pos ha r)).mpr
  convert hm using 1 <;> rw [mul_pow] <;> ring

theorem log_squared_exponential_cutoff (r : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, MF21Challenge.cutoff n ≤ j →
      (j : ℝ) ^ r * Real.exp (-c * j) ≤
        ((r.factorial : ℝ) / (c / 2) ^ r) / ((n : ℝ) + 2) := by
  have ha : 0 < c / 2 := by positivity
  have hl := (Real.tendsto_log_atTop.comp MF21Mesh.denominator_atTop).eventually
    (eventually_ge_atTop (1 / (c / 2)))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hl
  refine ⟨N, ?_⟩
  intro n hn j hj
  have hlog := hN n hn
  have hd : 0 < MF21Mesh.denominator n := MF21Mesh.denominator_pos n
  have hlog0 : 0 ≤ Real.log (MF21Mesh.denominator n) :=
    (div_pos (by norm_num) ha).le.trans hlog
  have hlog1 : 1 ≤ (c / 2) * Real.log (MF21Mesh.denominator n) := by
    exact ((div_le_iff₀ ha).mp hlog).trans_eq (mul_comm _ _)
  have hjr : (Real.log (MF21Mesh.denominator n)) ^ 2 ≤ (j : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast hj)
  have hprod : Real.log (MF21Mesh.denominator n) ≤ (c / 2) * j := by
    nlinarith [mul_le_mul_of_nonneg_left hjr ha.le,
      mul_nonneg hlog0 (sub_nonneg.mpr hlog1)]
  have he : Real.exp (-(c / 2) * j) ≤ (MF21Mesh.denominator n)⁻¹ := by
    rw [← Real.exp_log hd, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    linarith
  have hsplit : Real.exp (-c * j) = Real.exp (-(c / 2) * j) * Real.exp (-(c / 2) * j) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit, ← mul_assoc]
  have hb := exponential_power_bound r (c / 2) (j : ℝ) ha (Nat.cast_nonneg _)
  have hm := mul_le_mul hb he (Real.exp_pos _).le (by positivity : 0 ≤ (r.factorial : ℝ) / (c / 2) ^ r)
  simpa only [MF21Mesh.denominator, div_eq_mul_inv] using hm

end MF21Expansion
#print axioms MF21Expansion.exponential_power_bound
#print axioms MF21Expansion.log_squared_exponential_cutoff
