import MF21.FirstInverseColumn
import Mathlib.Data.Nat.Choose.Sum

/-! Exact binomial identity for the characteristic Laurent symbol. -/
noncomputable section
open scoped BigOperators
open Finset
namespace MF21Laurent

/-- The centered stencil polynomial is the binomial power. -/
theorem central_polynomial (m : ℕ) (z : ℂ) :
    (∑ l ∈ range (2*m+1), (MF21FirstColumn.central m l : ℂ) * z^l) =
      (-1 : ℂ)^m * (1-z)^(2*m) := by
  rw [show 1-z = -z+1 by ring, add_pow]
  simp only [one_pow, mul_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [MF21FirstColumn.central, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_natCast]
  rw [neg_pow, pow_add]
  ring

/-- The finite recurrence polynomial equals z^m times the actual symbol. -/
theorem central_sum_eq_laurent (m : ℕ) (z : ℂ) (hz : z ≠ 0) :
    (∑ l ∈ range (2*m+1), (MF21FirstColumn.central m l : ℂ) * z^l) =
      z^m * (2-z-z⁻¹)^m := by
  rw [central_polynomial, ← mul_pow]
  have h : z * (2-z-z⁻¹) = -(1-z)^2 := by
    field_simp
    ring
  rw [h, neg_pow ((1-z)^2) m, ← pow_mul]

/-- The centered recurrence is satisfied at all positions exactly when the
nonzero geometric ratio lies on the spectral Laurent level set. -/
theorem geometric_stencil (m k : ℕ) (z lam : ℂ) (hz : z ≠ 0)
    (h : (2-z-z⁻¹)^m = lam) :
    (∑ l ∈ range (2*m+1), (MF21FirstColumn.central m l : ℂ) * z^(k+l)) =
      lam * z^(k+m) := by
  simp only [pow_add]
  calc
    _ = z^k * ∑ l ∈ range (2*m+1), (MF21FirstColumn.central m l : ℂ) * z^l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ = _ := by rw [central_sum_eq_laurent m z hz, h]; ring

end MF21Laurent
#print axioms MF21Laurent.central_sum_eq_laurent
#print axioms MF21Laurent.geometric_stencil
