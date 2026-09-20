import MF21.FirstColumnAsymptotics
import MF21.TraceIntegralConstant
import MF21.TraceLimitSummation
import MF21.SpectralTrace

/-! The actual all-order Toeplitz inverse-trace limit, proved directly from
finite inverse columns, polynomial sums and telescoping. No continuous
Green-kernel convergence theorem is assumed. -/
noncomputable section
open scoped BigOperators Topology
open Filter Finset Matrix
namespace MF21TraceLimit

def inverseTrace (m n : ℕ) : ℝ := ((MF21Challenge.toeplitz m n)⁻¹).trace

/-- Exact increment formula for the trace sequence. -/
theorem inverseTrace_step (m n : ℕ) :
    inverseTrace m (n+1) - inverseTrace m n =
      (∑ j : Fin (n+1), (((MF21Challenge.toeplitz m (n+1))⁻¹) j 0)^2) /
        ((MF21Challenge.toeplitz m (n+1))⁻¹) 0 0 :=
  MF21InverseTrace.toeplitz_inverse_trace_step m n

/-- The actual normalized inverse-trace increments have the polynomial beta
integral as their limit. -/
theorem inverseTrace_increment_tendsto (r : ℕ) :
    Tendsto (fun n => (inverseTrace (r+1) (n+1) - inverseTrace (r+1) n) /
      (n : ℝ)^(2*r+1)) atTop
      (𝓝 ((∫ x in (0 : ℝ)..1, x^(2*r)*(1-x)^(2*r+2)) /
        (r.factorial : ℝ)^2)) := by
  have hnorm := MF21FirstAsymptotics.inverse_column_square_sum_tendsto r
  have hzero := MF21FirstAsymptotics.inverse_zero_zero_tendsto r
  have hquot := hnorm.div hzero (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at hquot
  have hr : Tendsto (fun n : ℕ => ((n : ℝ)+1)/(n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [inv_div, inv_one] using (tendsto_natCast_div_add_atTop (1 : ℝ)).inv₀
      (by norm_num : (1 : ℝ) ≠ 0)
  have ht := hquot.mul (hr.pow (2*r+1))
  simp only [one_pow, mul_one] at ht
  apply ht.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  simp only [Pi.div_apply]
  rw [inverseTrace_step]
  push_cast
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hn1 : (n : ℝ)+1 ≠ 0 := by positivity
  rw [div_pow]
  field_simp

/-- The finite-matrix inverse trace has exactly the rational limit used in
Section 5, for every positive order m=r+1. -/
theorem inverseTrace_tendsto (r : ℕ) :
    Tendsto (fun n => inverseTrace (r+1) n / ((n : ℝ)+2)^(2*(r+1)))
      atTop (𝓝 (MF21Audit.kernelTraceConstant (r+1) : ℝ)) := by
  have ht := MF21DiscreteLimits.sequence_of_increment_tendsto
    (2*r+1) (inverseTrace (r+1)) _ (inverseTrace_increment_tendsto r)
  have hconst : ((∫ x in (0 : ℝ)..1, x^(2*r)*(1-x)^(2*r+2)) /
        (r.factorial : ℝ)^2) / (2*r+2 : ℝ) =
      (MF21Audit.kernelTraceConstant (r+1) : ℝ) := by
    convert MF21DiscreteLimits.first_column_integral_constant r using 2
    congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [mul_pow, ← pow_mul, ← pow_mul]
    congr 1 <;> congr 1 <;> omega
  have ht' : Tendsto (fun n => inverseTrace (r+1) n / (n : ℝ)^(2*(r+1)))
      atTop (𝓝 (MF21Audit.kernelTraceConstant (r+1) : ℝ)) := by
    rw [show 2*r+1+1 = 2*(r+1) by omega] at ht
    push_cast at ht
    rw [show 2*r+2 = 2*(r+1) by omega] at hconst
    rw [show (2*r+1 : ℝ)+1 = 2*r+2 by ring, hconst] at ht
    exact ht
  exact MF21DiscreteLimits.normalized_shift_tendsto (2*(r+1)) _ 2 _ ht'

/-- The same limit, stated as the sum of reciprocals of the actual ordered
eigenvalues used in the canonical target. -/
theorem eigenvalue_inverse_sum_tendsto (m : ℕ) (hm : 0 < m) :
    Tendsto (fun n => (∑ j : Fin n, (MF21Challenge.eigenvalue m n j)⁻¹) /
      ((n : ℝ)+2)^(2*m)) atTop
      (𝓝 (MF21Audit.kernelTraceConstant m : ℝ)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  simpa only [inverseTrace, MF21Challenge.toeplitz_inverse_trace] using inverseTrace_tendsto r

end MF21TraceLimit
#print axioms MF21TraceLimit.inverseTrace_increment_tendsto
#print axioms MF21TraceLimit.inverseTrace_tendsto
#print axioms MF21TraceLimit.eigenvalue_inverse_sum_tendsto
