import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
The logarithmic bulk scale gain used after manuscript equation (25).

This module proves a scalar analytic estimate. It does not assert a Toeplitz
eigenvalue approximation or any part of the coefficient construction. The
statement was recorded in BULK_STATEMENT.md before writing the proof.
-/

set_option autoImplicit false
open Filter
open scoped Topology

namespace MF21Restart

/-- Above the fixed logarithmic-squared threshold, exponential decay absorbs
both an arbitrary natural polynomial in the index and the extra factor n+2.
The cutoff depends only on c,q; the estimate holds for every index above it,
without an additional upper bound on the index. -/
theorem exists_log_sq_bulk_scale_gain
    (c : ℝ) (hc : 0 < c) (q : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ,
      Nat.ceil ((Real.log (n + 2 : ℝ)) ^ 2) ≤ j →
      (n + 2 : ℝ) * (j : ℝ) ^ q *
        Real.exp (-c * (j : ℝ)) ≤ 1 := by
  have hhalf : 0 < c / 2 := by positivity
  -- The first half of the exponential absorbs the polynomial.
  have hpoly : Tendsto
      (fun x : ℝ => x ^ q * Real.exp (-(c / 2) * x))
      atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (q : ℝ) (c / 2) hhalf
  have hsmall : ∀ᶠ x : ℝ in atTop,
      x ^ q * Real.exp (-(c / 2) * x) < 1 :=
    (tendsto_order.mp hpoly).2 1 zero_lt_one
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.mp hsmall
  -- One eventual bound on log(n+2) will ensure both required estimates.
  have hshift : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
    apply Filter.tendsto_atTop_mono
      (fun n : ℕ => show (n : ℝ) ≤ (n : ℝ) + 2 by linarith)
    exact tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log (n + 2 : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hshift
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (hlog (Filter.eventually_ge_atTop (max A (max 1 (2 / c)))))
  refine ⟨N, ?_⟩
  intro n hn j hj
  let L : ℝ := Real.log (n + 2 : ℝ)
  have hL : max A (max 1 (2 / c)) ≤ L := hN n hn
  have hLA : A ≤ L := le_trans (le_max_left _ _) hL
  have hLrest : max (1 : ℝ) (2 / c) ≤ L :=
    le_trans (le_max_right _ _) hL
  have hLone : 1 ≤ L := le_trans (le_max_left _ _) hLrest
  have hLc : 2 / c ≤ L := le_trans (le_max_right _ _) hLrest
  have hLzero : 0 ≤ L := le_trans zero_le_one hLone
  have hLsq : L ≤ L ^ 2 := by
    calc
      L = 1 * L := (one_mul L).symm
      _ ≤ L * L := mul_le_mul_of_nonneg_right hLone hLzero
      _ = L ^ 2 := (pow_two L).symm
  have hceil : L ^ 2 ≤ (Nat.ceil (L ^ 2) : ℝ) := Nat.le_ceil _
  have hjceil : (Nat.ceil (L ^ 2) : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hj
  have hLj : L ^ 2 ≤ (j : ℝ) := le_trans hceil hjceil
  have hjA : A ≤ (j : ℝ) := hLA.trans (hLsq.trans hLj)
  have hpolyj : (j : ℝ) ^ q * Real.exp (-(c / 2) * (j : ℝ)) ≤ 1 :=
    (hA (j : ℝ) hjA).le
  -- The second half absorbs n+2 because (c/2)*j ≥ log(n+2).
  have htwo : (2 : ℝ) ≤ L * c := (div_le_iff₀ hc).mp hLc
  have hhalfOne : 1 ≤ (c / 2) * L := by nlinarith
  have hphase : L ≤ (c / 2) * (j : ℝ) := by
    calc
      L = 1 * L := (one_mul L).symm
      _ ≤ ((c / 2) * L) * L :=
        mul_le_mul_of_nonneg_right hhalfOne hLzero
      _ = (c / 2) * L ^ 2 := by ring
      _ ≤ (c / 2) * (j : ℝ) :=
        mul_le_mul_of_nonneg_left hLj hhalf.le
  have hscale : (n + 2 : ℝ) * Real.exp (-(c / 2) * (j : ℝ)) ≤ 1 := by
    calc
      (n + 2 : ℝ) * Real.exp (-(c / 2) * (j : ℝ)) =
          Real.exp L * Real.exp (-(c / 2) * (j : ℝ)) := by
        rw [show Real.exp L = (n + 2 : ℝ) from Real.exp_log (by positivity)]
      _ = Real.exp (L + (-(c / 2) * (j : ℝ))) := by rw [Real.exp_add]
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hsplit : Real.exp (-c * (j : ℝ)) =
      Real.exp (-(c / 2) * (j : ℝ)) *
        Real.exp (-(c / 2) * (j : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    (n + 2 : ℝ) * (j : ℝ) ^ q * Real.exp (-c * (j : ℝ)) =
        ((j : ℝ) ^ q * Real.exp (-(c / 2) * (j : ℝ))) *
          ((n + 2 : ℝ) * Real.exp (-(c / 2) * (j : ℝ))) := by
      rw [hsplit]
      ring
    _ ≤ 1 * 1 := mul_le_mul hpolyj hscale (by positivity) zero_le_one
    _ = 1 := by simp

end MF21Restart
