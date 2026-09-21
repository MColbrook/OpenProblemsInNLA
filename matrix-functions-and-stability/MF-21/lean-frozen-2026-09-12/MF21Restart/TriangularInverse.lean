import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

/-! Formal-series coefficients give exact finite triangular inverses.
The statement lock is TRIANGULAR_INVERSE_STATEMENTS.md. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

def powerSeriesUpperMatrix (n : ℕ) (f : PowerSeries ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i.val ≤ j.val then PowerSeries.coeff (j.val - i.val) f else 0

theorem powerSeriesUpperMatrix_one (n : ℕ) :
    powerSeriesUpperMatrix n 1 = (1 : Matrix (Fin n) (Fin n) ℝ) := by
  classical
  ext i j
  simp only [powerSeriesUpperMatrix, PowerSeries.coeff_one, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    simp
  · have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    by_cases hle : i.val ≤ j.val
    · have hsub : j.val - i.val ≠ 0 := by omega
      simp [hij, hle, hsub]
    · simp [hij, hle]

theorem powerSeriesUpperMatrix_mul (n : ℕ) (f g : PowerSeries ℝ) :
    powerSeriesUpperMatrix n (f * g) =
      powerSeriesUpperMatrix n f * powerSeriesUpperMatrix n g := by
  classical
  ext i j
  by_cases hij : i.val ≤ j.val
  · simp only [powerSeriesUpperMatrix, if_pos hij, Matrix.mul_apply]
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have hfilter :
        (∑ k : Fin n,
          (if i.val ≤ k.val then PowerSeries.coeff (k.val - i.val) f else 0) *
          (if k.val ≤ j.val then PowerSeries.coeff (j.val - k.val) g else 0)) =
        ∑ k ∈ (Finset.univ : Finset (Fin n)).filter
          (fun k => i.val ≤ k.val ∧ k.val ≤ j.val),
          PowerSeries.coeff (k.val - i.val) f * PowerSeries.coeff (j.val - k.val) g := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hik : i.val ≤ k.val <;> by_cases hkj : k.val ≤ j.val <;> simp [hik, hkj]
    rw [hfilter]
    symm
    apply Finset.sum_bij (fun k _ => k.val - i.val)
    · intro k hk
      have hk' := (Finset.mem_filter.mp hk).2
      exact Finset.mem_range.mpr (by omega)
    · intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      exact Fin.ext (by omega)
    · intro r hr
      have hr' := Finset.mem_range.mp hr
      let k : Fin n := ⟨i.val + r, by have := j.isLt; omega⟩
      refine ⟨k, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        dsimp [k]
        constructor <;> omega
      · dsimp [k]
        omega
    · intro k hk
      have hk' := (Finset.mem_filter.mp hk).2
      have hsub : j.val - k.val = j.val - i.val - (k.val - i.val) := by omega
      dsimp only
      rw [hsub]
  · simp only [powerSeriesUpperMatrix, if_neg hij, Matrix.mul_apply]
    symm
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : i.val ≤ k.val
    · have hkj : ¬k.val ≤ j.val := by omega
      simp [hkj]
    · simp [hik]

def binomialUpperMatrix (m n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  powerSeriesUpperMatrix n (PowerSeries.invOneSubPow ℝ m).val

def differenceUpperMatrix (m n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  powerSeriesUpperMatrix n ((1 - PowerSeries.X : PowerSeries ℝ) ^ m)

theorem binomialUpperMatrix_mul_difference (m n : ℕ) :
    binomialUpperMatrix m n * differenceUpperMatrix m n = 1 := by
  unfold binomialUpperMatrix differenceUpperMatrix
  rw [← powerSeriesUpperMatrix_mul,
    ← PowerSeries.invOneSubPow_inv_eq_one_sub_pow ℝ m,
    Units.val_inv, powerSeriesUpperMatrix_one]

theorem differenceUpperMatrix_mul_binomial (m n : ℕ) :
    differenceUpperMatrix m n * binomialUpperMatrix m n = 1 := by
  unfold binomialUpperMatrix differenceUpperMatrix
  rw [← powerSeriesUpperMatrix_mul,
    ← PowerSeries.invOneSubPow_inv_eq_one_sub_pow ℝ m,
    Units.inv_val, powerSeriesUpperMatrix_one]

theorem binomialUpperMatrix_apply (m n : ℕ) (hm : 1 ≤ m) (i j : Fin n) :
    binomialUpperMatrix m n i j =
      if i.val ≤ j.val then
        ((m - 1 + (j.val - i.val)).choose (m - 1) : ℝ) else 0 := by
  unfold binomialUpperMatrix powerSeriesUpperMatrix
  rw [PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℝ m (by omega : 0 < m)]
  simp only [PowerSeries.coeff_mk]

theorem powerSeries_coeff_one_sub_pow (m k : ℕ) :
    PowerSeries.coeff k ((1 - PowerSeries.X : PowerSeries ℝ) ^ m) =
      (-1 : ℝ) ^ k * (m.choose k : ℝ) := by
  have hrescale : PowerSeries.rescale (-1 : ℝ)
      ((1 + PowerSeries.X : PowerSeries ℝ) ^ m) =
        (1 - PowerSeries.X : PowerSeries ℝ) ^ m := by
    rw [map_pow, map_add, map_one, PowerSeries.rescale_neg_one_X, sub_eq_add_neg]
  rw [← hrescale, PowerSeries.coeff_rescale]
  have hpoly : (((1 + Polynomial.X : Polynomial ℝ) ^ m : Polynomial ℝ) : PowerSeries ℝ) =
      (1 + PowerSeries.X : PowerSeries ℝ) ^ m := by simp
  rw [← hpoly, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

theorem differenceUpperMatrix_apply (m n : ℕ) (i j : Fin n) :
    differenceUpperMatrix m n i j =
      if i.val ≤ j.val then
        (-1 : ℝ) ^ (j.val - i.val) * (m.choose (j.val - i.val) : ℝ) else 0 := by
  unfold differenceUpperMatrix powerSeriesUpperMatrix
  rw [powerSeries_coeff_one_sub_pow]

#print axioms powerSeriesUpperMatrix_one
#print axioms powerSeriesUpperMatrix_mul
#print axioms binomialUpperMatrix_mul_difference
#print axioms differenceUpperMatrix_mul_binomial
#print axioms binomialUpperMatrix_apply
#print axioms powerSeries_coeff_one_sub_pow
#print axioms differenceUpperMatrix_apply

end MF21Restart
