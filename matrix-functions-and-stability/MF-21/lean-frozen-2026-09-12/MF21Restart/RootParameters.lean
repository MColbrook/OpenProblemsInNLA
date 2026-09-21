import MF21Restart.StableRootSmooth
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
The exact exponential parameters in manuscript (2) and (8), followed by
their substitution into the actual quadratic root curve. The real angles
are explicitly cast to complex numbers; no integer division or assumed
phase identity is used. ROOT_PARAMETER_STATEMENTS.md precedes this proof.
-/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

def rootOmega (m ell : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * (ell : ℝ) / (m : ℝ) : ℝ) : ℂ) * Complex.I)

def rootKappa (m ell : ℕ) : ℂ :=
  Complex.exp (((Real.pi * (ell : ℝ) / (m : ℝ) - Real.pi / 2 : ℝ) : ℂ) *
    Complex.I)

/-- The published indices put kappa strictly in the right half-plane. -/
theorem rootKappa_re_pos (m ell : ℕ)
    (hell : 1 ≤ ell) (hellm : ell < m) :
    0 < (rootKappa m ell).re := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hellpos : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast (show 0 < ell by omega)
  have helllt : (ell : ℝ) < (m : ℝ) := by exact_mod_cast hellm
  rw [rootKappa, Complex.exp_ofReal_mul_I_re, Real.cos_sub_pi_div_two]
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact div_pos (mul_pos Real.pi_pos hellpos) hmpos
  · exact (div_lt_iff₀ hmpos).2 (mul_lt_mul_of_pos_left helllt Real.pi_pos)

theorem rootKappa_norm (m ell : ℕ) : ‖rootKappa m ell‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I
    (Real.pi * (ell : ℝ) / (m : ℝ) - Real.pi / 2)

theorem rootKappa_ne_zero (m ell : ℕ) : rootKappa m ell ≠ 0 :=
  Complex.exp_ne_zero _

/-- The sign in kappa²=-omega comes from the actual pi-shift of the exponential. -/
theorem rootKappa_sq (m ell : ℕ) :
    rootKappa m ell ^ 2 = -rootOmega m ell := by
  let alpha : ℝ := Real.pi * (ell : ℝ) / (m : ℝ) - Real.pi / 2
  let beta : ℝ := 2 * Real.pi * (ell : ℝ) / (m : ℝ)
  change Complex.exp ((alpha : ℂ) * Complex.I) ^ 2 =
    -Complex.exp ((beta : ℂ) * Complex.I)
  rw [pow_two, ← Complex.exp_add]
  have hangle :
      (alpha : ℂ) * Complex.I + (alpha : ℂ) * Complex.I =
        (beta : ℂ) * Complex.I - (Real.pi : ℂ) * Complex.I := by
    dsimp [alpha, beta]
    push_cast
    ring
  rw [hangle, Complex.exp_sub_pi_mul_I]

/-- Substituting the exact manuscript parameters gives its reciprocal equation (2). -/
theorem stableRootCurve_rootOmega_equation (m ell : ℕ) (theta : ℝ) :
    2 - stableRootCurve (rootKappa m ell) theta -
        (stableRootCurve (rootKappa m ell) theta)⁻¹ =
      rootOmega m ell * ((2 - 2 * Real.cos theta : ℝ) : ℂ) := by
  have hcos := Real.cos_two_mul_eq_one_sub (theta / 2)
  rw [show 2 * (theta / 2) = theta by ring] at hcos
  have hhalf : 4 * Real.sin (theta / 2) ^ 2 = 2 - 2 * Real.cos theta := by
    nlinarith
  rw [stableRootCurve_equation, rootKappa_sq]
  calc
    -4 * (-rootOmega m ell) * (Real.sin (theta / 2) : ℂ) ^ 2 =
        rootOmega m ell * ((4 * Real.sin (theta / 2) ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    _ = rootOmega m ell * ((2 - 2 * Real.cos theta : ℝ) : ℂ) := by rw [hhalf]

#print axioms rootKappa_re_pos
#print axioms rootKappa_norm
#print axioms rootKappa_ne_zero
#print axioms rootKappa_sq
#print axioms stableRootCurve_rootOmega_equation

end MF21Restart
