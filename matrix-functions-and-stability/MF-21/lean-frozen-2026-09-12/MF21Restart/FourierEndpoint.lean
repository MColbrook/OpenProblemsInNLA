import MF21Restart.FourierStencil

/-!
The exact nonzero outer coefficients of the concrete MF-21 Fourier stencil.
The recurrence and support used here have already been derived from the
normalized Fourier integral, rather than assumed for an abstract array.
-/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

/-- At the largest possible frequency, the stencil recurrence has exactly
one surviving term. This also includes the zeroth-order coefficient. -/
theorem fourierCoeff_right_endpoint (m : ℕ) :
    fourierCoeff m (m : ℤ) = (-1 : ℝ) ^ m := by
  induction m with
  | zero => simp [fourierCoeff_zero]
  | succ m ih =>
      have hm : (0 : ℤ) ≤ (m : ℤ) := by exact_mod_cast Nat.zero_le m
      have hnear : fourierCoeff m ((m : ℤ) + 1) = 0 := by
        apply fourierCoeff_support
        rw [abs_of_nonneg (by omega)]
        omega
      have hfar : fourierCoeff m (((m : ℤ) + 1) + 1) = 0 := by
        apply fourierCoeff_support
        rw [abs_of_nonneg (by omega)]
        omega
      rw [Nat.cast_succ, fourierCoeff_succ, hnear, hfar]
      simp [ih, pow_succ]

/-- The negative-frequency endpoint agrees by the evenness of the actual
Fourier coefficient. -/
theorem fourierCoeff_left_endpoint (m : ℕ) :
    fourierCoeff m (-(m : ℤ)) = (-1 : ℝ) ^ m := by
  rw [fourierCoeff_neg, fourierCoeff_right_endpoint]

theorem fourierCoeff_right_endpoint_ne_zero (m : ℕ) :
    fourierCoeff m (m : ℤ) ≠ 0 := by
  rw [fourierCoeff_right_endpoint]
  exact pow_ne_zero _ (by norm_num)

theorem fourierCoeff_left_endpoint_ne_zero (m : ℕ) :
    fourierCoeff m (-(m : ℤ)) ≠ 0 := by
  rw [fourierCoeff_neg]
  exact fourierCoeff_right_endpoint_ne_zero m

#print axioms fourierCoeff_right_endpoint
#print axioms fourierCoeff_left_endpoint
#print axioms fourierCoeff_right_endpoint_ne_zero
#print axioms fourierCoeff_left_endpoint_ne_zero

end MF21Restart
