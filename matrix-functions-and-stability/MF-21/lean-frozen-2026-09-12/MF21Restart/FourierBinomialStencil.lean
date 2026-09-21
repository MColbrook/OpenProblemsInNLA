import MF21Restart.FourierRecurrence
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Finite.Basic

/-!
The binomial stencil is derived from the actual integral Fourier coefficient.
The already proved Laurent identity identifies a finite polynomial on every
nonzero complex number; coefficient extraction then gives the exact formula.
The original coefficient and Toeplitz matrix are not redefined.

The statement lock is `FOURIER_BINOMIAL_STENCIL_STATEMENTS.md`. This is a
coefficient bridge toward the known Duduchava–Roch inverse, not a matrix
inverse or an asymptotic theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

/-- Shift the actual Fourier support [-m,m] to the natural degrees [0,2m]. -/
def fourierStencilPolynomial (m : ℕ) : Polynomial ℂ :=
  ∑ t : Fin (2 * m + 1),
    Polynomial.C (fourierCoeff m ((t.val : ℤ) - (m : ℤ)) : ℂ) *
      Polynomial.X ^ t.val

/-- Equality away from zero suffices to identify the actual coefficient
polynomial; no Laurent expression is evaluated at its excluded point. -/
theorem fourierStencilPolynomial_eq (m : ℕ) :
    fourierStencilPolynomial m =
      Polynomial.C ((-1 : ℂ) ^ m) * (1 - Polynomial.X) ^ (2 * m) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.finite_singleton (0 : ℂ)).infinite_compl.mono
  intro z hz
  have hz0 : z ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hz
  change (fourierStencilPolynomial m).eval z =
    (Polynomial.C ((-1 : ℂ) ^ m) * (1 - Polynomial.X) ^ (2 * m)).eval z
  simp only [fourierStencilPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one]
  rw [fourierCoeff_shifted_laurent_sum m z hz0]
  have hbase : z * (2 - z - z⁻¹) = -(1 - z) ^ 2 := by
    rw [mul_sub, mul_sub, mul_inv_cancel₀ hz0]
    ring
  calc
    z ^ m * (2 - z - z⁻¹) ^ m = (z * (2 - z - z⁻¹)) ^ m :=
      (mul_pow _ _ _).symm
    _ = (-(1 - z) ^ 2) ^ m := by rw [hbase]
    _ = (-1 : ℂ) ^ m * (1 - z) ^ (2 * m) := by
      rw [neg_pow, ← pow_mul]

private theorem fourierStencilPolynomial_coeff
    (m t : ℕ) (ht : t ≤ 2 * m) :
    (fourierStencilPolynomial m).coeff t =
      (fourierCoeff m ((t : ℤ) - (m : ℤ)) : ℂ) := by
  classical
  let ti : Fin (2 * m + 1) := ⟨t, by omega⟩
  simp only [fourierStencilPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single ti]
  · simp [ti]
  · intro i _ hi
    have hti : t ≠ i.val := by
      intro h
      apply hi
      apply Fin.ext
      exact h.symm
    simp only [if_neg hti]
  · simp

private theorem coeff_one_sub_X_even_pow
    (m t : ℕ) (ht : t ≤ 2 * m) :
    ((1 - Polynomial.X : Polynomial ℂ) ^ (2 * m)).coeff t =
      (-1 : ℂ) ^ t * ((2 * m).choose t : ℂ) := by
  have heven : (1 - Polynomial.X : Polynomial ℂ) ^ (2 * m) =
      (Polynomial.X + Polynomial.C (-1 : ℂ)) ^ (2 * m) := by
    rw [pow_mul, pow_mul]
    congr 1
    simp only [Polynomial.C_neg, Polynomial.C_1]
    ring
  have hsign : (-1 : ℂ) ^ (2 * m - t) = (-1 : ℂ) ^ t := by
    calc
      (-1 : ℂ) ^ (2 * m - t) = (-1 : ℂ) ^ ((2 * m - t) % 2) :=
        neg_one_pow_eq_pow_mod_two _
      _ = (-1 : ℂ) ^ (t % 2) := by congr 1; omega
      _ = (-1 : ℂ) ^ t := (neg_one_pow_eq_pow_mod_two t).symm
  rw [heven, Polynomial.coeff_X_add_C_pow, hsign]

/-- The literal integral Fourier coefficient, including order zero and
both support endpoints. The subtraction in the frequency is in integers. -/
theorem fourierCoeff_shifted_binomial (m t : ℕ) (ht : t ≤ 2 * m) :
    fourierCoeff m ((t : ℤ) - (m : ℤ)) =
      (-1 : ℝ) ^ (m + t) * ((2 * m).choose t : ℝ) := by
  have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff t)
    (fourierStencilPolynomial_eq m)
  rw [fourierStencilPolynomial_coeff m t ht, Polynomial.coeff_C_mul,
    coeff_one_sub_X_even_pow m t ht] at hcoeff
  have hcomplex : (fourierCoeff m ((t : ℤ) - (m : ℤ)) : ℂ) =
      (-1 : ℂ) ^ (m + t) * ((2 * m).choose t : ℂ) := by
    simpa only [pow_add, mul_assoc] using hcoeff
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_one, Complex.ofReal_natCast] using hcomplex

#print axioms fourierStencilPolynomial_eq
#print axioms fourierCoeff_shifted_binomial

end MF21Restart
