import Mathlib.NumberTheory.Bernoulli
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Finite polynomial-sum limits used in the direct inverse-trace proof. -/
noncomputable section
open scoped BigOperators Topology
open Filter Finset Polynomial
namespace MF21DiscreteLimits

/-- Faulhaber's exact formula, cast to the real numbers. -/
theorem sum_power_real (n p : ℕ) :
    (∑ k ∈ range n, (k : ℝ) ^ p) =
      ∑ i ∈ range (p + 1), (bernoulli i : ℝ) * ((p+1).choose i : ℝ) *
        (n : ℝ) ^ (p+1-i) / (p+1) := by
  exact_mod_cast sum_range_pow n p

/-- The normalized finite sum is an explicit polynomial in 1/n. -/
theorem normalized_power_sum (p n : ℕ) (hn : n ≠ 0) :
    (∑ k ∈ range n, (k : ℝ) ^ p) / (n : ℝ) ^ (p+1) =
      ∑ i ∈ range (p+1),
        ((bernoulli i : ℝ) * ((p+1).choose i : ℝ) / (p+1)) * ((n : ℝ)⁻¹) ^ i := by
  rw [sum_power_real, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ p+1 := by have := Finset.mem_range.mp hi; omega
  have hnp : (n : ℝ) ^ (p+1) = (n : ℝ) ^ (p+1-i) * (n : ℝ) ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi']
  rw [hnp, inv_pow]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp [hnR]

theorem normalized_power_sum_tendsto (p : ℕ) :
    Tendsto (fun n : ℕ => (∑ k ∈ range n, (k : ℝ) ^ p) / (n : ℝ) ^ (p+1))
      atTop (𝓝 ((p+1 : ℝ)⁻¹)) := by
  have ht : Tendsto (fun n : ℕ => ∑ i ∈ range (p+1),
        ((bernoulli i : ℝ) * ((p+1).choose i : ℝ) / (p+1)) * ((n : ℝ)⁻¹) ^ i)
      atTop (𝓝 (∑ i ∈ range (p+1),
        ((bernoulli i : ℝ) * ((p+1).choose i : ℝ) / (p+1)) * (0 : ℝ) ^ i)) := by
    apply tendsto_finsetSum
    intro i hi
    exact tendsto_const_nhds.mul ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).pow i)
  have he : (∑ i ∈ range (p+1),
        ((bernoulli i : ℝ) * ((p+1).choose i : ℝ) / (p+1)) * (0 : ℝ) ^ i) =
        (p+1 : ℝ)⁻¹ := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro i hi hne
      simp [zero_pow hne]
    · simp
  rw [he] at ht
  apply ht.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (normalized_power_sum p n hn).symm


/-- Monomial left Riemann sums on the unit interval. -/
theorem monomial_riemann_tendsto (p : ℕ) :
    Tendsto (fun n : ℕ => (∑ j ∈ range n, ((j : ℝ) / n) ^ p) / n)
      atTop (𝓝 ((p+1 : ℝ)⁻¹)) := by
  convert normalized_power_sum_tendsto p using 1
  funext n
  simp only [div_pow, ← Finset.sum_div]
  rw [div_div, pow_succ]

/-- Riemann sums still converge when the finitely many polynomial coefficients
vary with n and each coefficient converges. -/
theorem finite_polynomial_riemann_tendsto (d : ℕ) (a : ℕ → ℕ → ℝ) (b : ℕ → ℝ)
    (h : ∀ i ∈ range d, Tendsto (fun n => a n i) atTop (𝓝 (b i))) :
    Tendsto (fun n : ℕ =>
      (∑ j ∈ range n, ∑ i ∈ range d, a n i * ((j : ℝ) / n) ^ i) / n)
      atTop (𝓝 (∑ i ∈ range d, b i / (i+1 : ℝ))) := by
  have he (n : ℕ) :
      (∑ j ∈ range n, ∑ i ∈ range d, a n i * ((j : ℝ) / n) ^ i) / n =
        ∑ i ∈ range d, a n i * ((∑ j ∈ range n, ((j : ℝ) / n) ^ i) / n) := by
    rw [Finset.sum_comm, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.mul_sum]
    ring
  simp_rw [he]
  apply tendsto_finsetSum
  intro i hi
  simpa only [div_eq_mul_inv] using (h i hi).mul (monomial_riemann_tendsto i)

/-- A bounded-degree polynomial sequence can be integrated by its coefficient
limits using the exact discrete monomial sums above. -/
theorem polynomial_riemann_tendsto (d : ℕ) (P : ℕ → ℝ[X]) (Q : ℝ[X])
    (hdeg : ∀ n, (P n).natDegree < d) (hQ : Q.natDegree < d)
    (hc : ∀ i ∈ range d,
      Tendsto (fun n => (P n).coeff i) atTop (𝓝 (Q.coeff i))) :
    Tendsto (fun n : ℕ => (∑ j ∈ range n, (P n).eval ((j : ℝ) / n)) / n)
      atTop (𝓝 (∫ x in (0 : ℝ)..1, Q.eval x)) := by
  have hsum : (∫ x in (0 : ℝ)..1, Q.eval x) =
      ∑ i ∈ range d, Q.coeff i / (i+1 : ℝ) := by
    simp_rw [Polynomial.eval_eq_sum_range' hQ]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [intervalIntegral.integral_const_mul, integral_pow]
      simp [div_eq_mul_inv]
    · intro i hi
      exact (continuous_const.mul (continuous_id.pow i)).intervalIntegrable _ _
  rw [hsum]
  simp_rw [Polynomial.eval_eq_sum_range' (hdeg _)]
  exact finite_polynomial_riemann_tendsto d (fun n i => (P n).coeff i) Q.coeff hc

end MF21DiscreteLimits
#print axioms MF21DiscreteLimits.normalized_power_sum_tendsto

#print axioms MF21DiscreteLimits.polynomial_riemann_tendsto
