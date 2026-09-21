import MF21Restart.Definitions
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Basic

/-!
The analytic implication used in manuscript (30). These lemmas derive the
fixed-index limit from the implicit phase equation and a Taylor-sized error.
They do not assume the limit itself or assert that the spectral hypotheses
have already been proved. The manuscript's earlier sections must supply them.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace MF21Restart

lemma two_mul_sin_half (y : ℝ) :
    2 * Real.sin (y / 2) = y * Real.sinc (y / 2) := by
  by_cases hy : y = 0
  · simp [hy]
  · rw [Real.sinc_of_ne_zero (div_ne_zero hy (by norm_num))]
    field_simp

/-- Dividing the actual implicit phase equation gives its endpoint limit.
Here `b = π*j`; positivity of `h` justifies division. -/
theorem implicit_phase_ratio_limit
    {h y : ℕ → ℝ} {η : ℝ → ℝ} {b : ℝ}
    (hy : Tendsto y atTop (𝓝 0))
    (hη : ContinuousAt η 0)
    (hpos : ∀ᶠ n in atTop, 0 < h n)
    (heq : ∀ᶠ n in atTop, y n = b * h n + h n * η (y n)) :
    Tendsto (fun n => y n / h n) atTop (𝓝 (b + η 0)) := by
  have hevent : (fun n => y n / h n) =ᶠ[atTop] (fun n => b + η (y n)) := by
    filter_upwards [hpos, heq] with n hn hEq
    calc
      y n / h n = (b * h n + h n * η (y n)) / h n := congrArg (· / h n) hEq
      _ = b + η (y n) := by field_simp
  exact (tendsto_const_nhds.add (hη.tendsto.comp hy)).congr' hevent.symm

/-- The order-`2m` zero of the symbol converts the phase limit to a spectral scale.
The sinc identity also handles terms for which `y n = 0`. -/
theorem symbol_scaled_limit
    (m : ℕ) {h y : ℕ → ℝ} {a : ℝ}
    (hy : Tendsto y atTop (𝓝 0))
    (hratio : Tendsto (fun n => y n / h n) atTop (𝓝 a)) :
    Tendsto (fun n => symbol m (y n) / (h n) ^ (2 * m))
      atTop (𝓝 (a ^ (2 * m))) := by
  have hsinc : Tendsto (fun n => Real.sinc (y n / 2)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using
      Real.continuous_sinc.continuousAt.tendsto.comp (hy.div_const 2)
  have hfactor : ∀ n, symbol m (y n) / (h n) ^ (2 * m) =
      ((y n / h n) * Real.sinc (y n / 2)) ^ (2 * m) := by
    intro n
    rw [symbol, two_mul_sin_half, ← div_pow]
    congr 1
    ring
  simpa only [hfactor, mul_one] using (hratio.mul hsinc).pow (2 * m)

/-- A remainder of order `h^(2m+1)` disappears after scaling by `h^(2m)`.
This is where the assumed global critical-order estimate is used in (30). -/
theorem fixed_index_limit_of_implicit_phase
    (m : ℕ) {h y ev : ℕ → ℝ} {η : ℝ → ℝ} {b C : ℝ}
    (hh : Tendsto h atTop (𝓝 0))
    (hy : Tendsto y atTop (𝓝 0))
    (hη : ContinuousAt η 0)
    (hpos : ∀ᶠ n in atTop, 0 < h n)
    (heq : ∀ᶠ n in atTop, y n = b * h n + h n * η (y n))
    (herror : ∀ᶠ n in atTop,
      |ev n - symbol m (y n)| ≤ C * (h n) ^ (2 * m + 1)) :
    Tendsto (fun n => ev n / (h n) ^ (2 * m))
      atTop (𝓝 ((b + η 0) ^ (2 * m))) := by
  have hbase := symbol_scaled_limit m hy (implicit_phase_ratio_limit hy hη hpos heq)
  have herr : Tendsto (fun n => (ev n - symbol m (y n)) / (h n) ^ (2 * m))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm'
      (a := fun n => C * h n)
    · filter_upwards [hpos, herror] with n hn he
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hn (2 * m))]
      apply (div_le_iff₀ (pow_pos hn (2 * m))).2
      calc
        |ev n - symbol m (y n)| ≤ C * (h n) ^ (2 * m + 1) := he
        _ = (C * h n) * (h n) ^ (2 * m) := by rw [pow_succ]; ring
    · simpa using tendsto_const_nhds.mul hh
  have hadd := hbase.add herr
  have hidentity : (fun n => symbol m (y n) / (h n) ^ (2 * m) +
      (ev n - symbol m (y n)) / (h n) ^ (2 * m)) =
      (fun n => ev n / (h n) ^ (2 * m)) := by
    funext n
    ring
  rw [hidentity, add_zero] at hadd
  exact hadd

/-- Equation (30) for the actual, correctly indexed Toeplitz eigenvalues.
The hypothetical critical uniform bound and the critical Taylor estimate
contain the *same full sum*, including `d (2*m)`; subtraction cancels it.
The implicit phase and Taylor construction remain explicit earlier obligations.
-/
theorem critical_bound_implies_fixed_index_limit
    (m j : ℕ) {d : ℕ → ℝ → ℝ} {y : ℕ → ℝ} {η : ℝ → ℝ} {B : ℝ}
    (hj : 1 ≤ j)
    (hU : UniformBound m d (2 * m))
    (hTaylor : ∀ᶠ n in atTop,
      |symbol m (y n) - expansion d (2 * m) n j| ≤
        B / (n + 2 : ℝ) ^ (2 * m + 1))
    (hy : Tendsto y atTop (𝓝 0))
    (hη : ContinuousAt η 0)
    (heq : ∀ᶠ n in atTop,
      y n = (Real.pi * j) * (1 / (n + 2 : ℝ)) +
        (1 / (n + 2 : ℝ)) * η (y n)) :
    Tendsto (fun n : ℕ => (n + 2 : ℝ) ^ (2 * m) * eigenvalue m n j)
      atTop (𝓝 ((Real.pi * j + η 0) ^ (2 * m))) := by
  obtain ⟨C, N, _hC, hC⟩ := hU
  have hh : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < (1 : ℝ) / (n + 2) :=
    .of_forall (fun n => by positivity)
  have herror : ∀ᶠ n : ℕ in atTop,
      |eigenvalue m n j - symbol m (y n)| ≤
        (C + B) * (1 / (n + 2 : ℝ)) ^ (2 * m + 1) := by
    filter_upwards [eventually_ge_atTop N, eventually_ge_atTop j, hTaylor]
      with n hn hjn ht
    calc
      |eigenvalue m n j - symbol m (y n)| ≤
          |eigenvalue m n j - expansion d (2 * m) n j| +
            |expansion d (2 * m) n j - symbol m (y n)| := abs_sub_le _ _ _
      _ ≤ C / (n + 2 : ℝ) ^ (2 * m + 1) +
          B / (n + 2 : ℝ) ^ (2 * m + 1) :=
        add_le_add (hC n j hn hj hjn) (by simpa only [abs_sub_comm] using ht)
      _ = (C + B) * (1 / (n + 2 : ℝ)) ^ (2 * m + 1) := by
        rw [one_div_pow]
        ring
  have hlimit := fixed_index_limit_of_implicit_phase m hh hy hη hpos heq herror
  simpa only [one_div, inv_pow, div_inv_eq_mul, mul_comm] using hlimit

#print axioms implicit_phase_ratio_limit
#print axioms symbol_scaled_limit
#print axioms fixed_index_limit_of_implicit_phase
#print axioms critical_bound_implies_fixed_index_limit

end MF21Restart
