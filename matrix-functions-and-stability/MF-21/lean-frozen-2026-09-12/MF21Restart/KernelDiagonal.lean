import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
The actual substitution u = 1 - x/t in manuscript (27), at y=x.

KERNEL_DIAGONAL_STATEMENTS.md locked these scalar integral statements before
the proof was written. The second theorem retains both factors of (t-x)
and both powers of x from (27). The formula's identification with the Green
kernel and its reflection across x=1/2 remain separate obligations.
-/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

/-- The manuscript's diagonal substitution, with its positive lower endpoint.
The case x=1, where the integral has equal endpoints, is included. -/
theorem kernel_diagonal_substitution (k : ℕ) (x : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1) :
    (∫ t in x..1, (t - x) ^ k / t ^ (k + 2)) =
      (1 - x) ^ (k + 1) / (((k + 1 : ℕ) : ℝ) * x) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have ht0 : ∀ t ∈ Set.uIcc x 1, t ≠ 0 := by
    intro t ht
    have ht' : t ∈ Set.Icc x 1 := by
      simpa only [Set.uIcc_of_le hx1] using ht
    exact ne_of_gt (lt_of_lt_of_le hx ht'.1)
  have hderiv : ∀ t ∈ Set.uIcc x 1,
      HasDerivAt (fun t : ℝ => 1 - x / t) (x / t ^ 2) t := by
    intro t ht
    have hdiv := (hasDerivAt_const t x).fun_div (hasDerivAt_id t) (ht0 t ht)
    -- Reduce Mathlib's definitionally equal real module instances in this transport.
    set_option backward.isDefEq.respectTransparency.types false in
      simpa only [id_eq, zero_mul, mul_one, zero_sub, neg_div, neg_neg] using
        hdiv.const_sub 1
  have hcontinuous : ContinuousOn (fun t : ℝ => x / t ^ 2) (Set.uIcc x 1) :=
    continuousOn_const.div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero 2 (ht0 t ht))
  have hpolynomial : Continuous (fun u : ℝ => u ^ k / x) :=
    (continuous_id.pow k).div_const x
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (a := x) (b := 1)
    (f := fun t : ℝ => 1 - x / t)
    (f' := fun t : ℝ => x / t ^ 2)
    (g := fun u : ℝ => u ^ k / x) hderiv hcontinuous hpolynomial
  calc
    (∫ t in x..1, (t - x) ^ k / t ^ (k + 2)) =
        ∫ t in x..1, ((1 - x / t) ^ k / x) * (x / t ^ 2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      change (t - x) ^ k / t ^ (k + 2) = ((1 - x / t) ^ k / x) * (x / t ^ 2)
      have htne := ht0 t ht
      have hbase : 1 - x / t = (t - x) / t := by
        field_simp [htne] <;> ring
      rw [hbase, div_pow, pow_add]
      field_simp [hx0, htne] <;> ring
    _ = ∫ u in (0 : ℝ)..(1 - x), u ^ k / x := by
      simpa only [Function.comp_apply, div_self hx0, sub_self, div_one] using hsub
    _ = (1 - x) ^ (k + 1) / (((k + 1 : ℕ) : ℝ) * x) := by
      rw [intervalIntegral.integral_div, integral_pow]
      simp only [zero_pow (Nat.succ_ne_zero k), sub_zero, div_div,
        Nat.cast_add, Nat.cast_one]

/-- The literal diagonal integral in (27) evaluates to the polynomial in (28).
This is a scalar identity; the kernel representation is not an assumption. -/
theorem kernel_diagonal_integral_value (m : ℕ) (hm : 1 ≤ m)
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    (x ^ m * x ^ m / ((m - 1).factorial : ℝ) ^ 2) *
      (∫ t in x..1,
        ((t - x) ^ (m - 1) * (t - x) ^ (m - 1)) / t ^ (2 * m)) =
    x ^ (2 * m - 1) * (1 - x) ^ (2 * m - 1) /
      (((2 * m - 1 : ℕ) : ℝ) * ((m - 1).factorial : ℝ) ^ 2) := by
  have hsum : (m - 1) + (m - 1) = 2 * m - 2 := by omega
  have hone : (2 * m - 2) + 1 = 2 * m - 1 := by omega
  have htwo : (2 * m - 2) + 2 = 2 * m := by omega
  have hprod (t : ℝ) :
      (t - x) ^ (m - 1) * (t - x) ^ (m - 1) = (t - x) ^ (2 * m - 2) := by
    rw [← pow_add, hsum]
  have hvalue := kernel_diagonal_substitution (2 * m - 2) x hx hx1
  simp only [hone, htwo] at hvalue
  simp_rw [hprod]
  rw [hvalue]
  have hpowx : x ^ m * x ^ m = x ^ (2 * m - 1) * x := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hfactorial : ((m - 1).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have horder : ((2 * m - 1 : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  rw [hpowx]
  field_simp [hx0, hfactorial, horder] <;> ring

#print axioms kernel_diagonal_substitution
#print axioms kernel_diagonal_integral_value

end MF21Restart
