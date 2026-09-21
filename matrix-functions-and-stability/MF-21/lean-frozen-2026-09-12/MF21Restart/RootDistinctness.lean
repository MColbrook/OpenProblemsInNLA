import MF21Restart.RootParameters
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
Initial root-list prerequisites for the actual exponential parameters:
the m-th root identity, injectivity on the half-open index range, and
kappa conjugacy. ROOT_DISTINCTNESS_STATEMENTS.md fixes this exact scope.
Stable-root and full characteristic-list distinctness remain separate.
-/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

theorem rootOmega_pow (m ell : ℕ) (hm : 1 ≤ m) :
    rootOmega m ell ^ m = 1 := by
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold rootOmega
  rw [← Complex.exp_nat_mul]
  have hangle :
      (m : ℂ) * (((2 * Real.pi * (ell : ℝ) / (m : ℝ) : ℝ) : ℂ) * Complex.I) =
        (ell : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    field_simp [hm0] <;> ring
  rw [hangle]
  exact Complex.exp_nat_mul_two_pi_mul_I ell

theorem rootOmega_injective (m : ℕ) :
    Function.Injective (fun ell : Fin m => rootOmega m ell.val) := by
  intro a b hab
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (show 0 < m by have := a.isLt; omega)
  have htwopi : (0 : ℝ) < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hangle_mem : ∀ ell : Fin m,
      2 * Real.pi * (ell.val : ℝ) / (m : ℝ) ∈ Set.Ico 0 (2 * Real.pi) := by
    intro ell
    constructor
    · positivity
    · apply (div_lt_iff₀ hmpos).2
      exact mul_lt_mul_of_pos_left (by exact_mod_cast ell.isLt) htwopi
  have hexp :
      Circle.exp (2 * Real.pi * (a.val : ℝ) / (m : ℝ)) =
        Circle.exp (2 * Real.pi * (b.val : ℝ) / (m : ℝ)) := by
    apply Circle.ext
    simpa only [Circle.coe_exp, rootOmega] using hab
  have hangle :
      2 * Real.pi * (a.val : ℝ) / (m : ℝ) =
        2 * Real.pi * (b.val : ℝ) / (m : ℝ) :=
    Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp)
      (hangle_mem a) (hangle_mem b) hexp
  have hnum : 2 * Real.pi * (a.val : ℝ) = 2 * Real.pi * (b.val : ℝ) :=
    (div_left_inj' (ne_of_gt hmpos)).mp hangle
  have hval : (a.val : ℝ) = (b.val : ℝ) := mul_left_cancel₀ (ne_of_gt htwopi) hnum
  apply Fin.ext
  exact_mod_cast hval

theorem rootKappa_conj (m ell : ℕ)
    (hell : 1 ≤ ell) (hellm : ell < m) :
    (starRingEnd ℂ) (rootKappa m ell) = rootKappa m (m - ell) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hangle :
      Real.pi * ((m - ell : ℕ) : ℝ) / (m : ℝ) - Real.pi / 2 =
        -(Real.pi * (ell : ℝ) / (m : ℝ) - Real.pi / 2) := by
    rw [Nat.cast_sub (Nat.le_of_lt hellm)]
    field_simp [hm0] <;> ring
  unfold rootKappa
  rw [← Complex.exp_conj, hangle]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

#print axioms rootOmega_pow
#print axioms rootOmega_injective
#print axioms rootKappa_conj

end MF21Restart
