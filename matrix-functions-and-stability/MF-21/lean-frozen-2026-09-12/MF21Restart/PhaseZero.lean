import MF21Restart.PhaseFactor
import MF21Restart.RootParameters
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field

/-!
The manuscript phase is the sum of the actual individual principal
arguments, extended smoothly through zero. The endpoint is computed from
the exact half-angle identity, never from the argument of a product.
PHASE_ZERO_STATEMENTS.md fixes the definitions and statements first.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

def manuscriptPsi (m : ℕ) (θ : ℝ) : ℝ :=
  ∑ ell : Fin (m - 1),
    individualPhase (rootKappa m (ell.val + 1)) θ

def manuscriptEta (m : ℕ) (θ : ℝ) : ℝ :=
  θ + 2 * manuscriptPsi m θ

/-- The exact polar factorization used to select the individual phase at zero. -/
theorem rootKappa_add_I (m ell : ℕ) :
    rootKappa m ell + Complex.I =
      ((2 * Real.sin (Real.pi * (ell : ℝ) / (2 * (m : ℝ))) : ℝ) : ℂ) *
        Complex.exp
          (((Real.pi * (ell : ℝ) / (2 * (m : ℝ)) : ℝ) : ℂ) * Complex.I) := by
  let alpha : ℝ := Real.pi * (ell : ℝ) / (2 * (m : ℝ))
  have hangle : Real.pi * (ell : ℝ) / (m : ℝ) = 2 * alpha := by
    dsimp [alpha]
    rw [div_mul_eq_div_div_swap]
    ring
  change Complex.exp
      (((Real.pi * (ell : ℝ) / (m : ℝ) - Real.pi / 2 : ℝ) : ℂ) * Complex.I) +
      Complex.I =
    ((2 * Real.sin alpha : ℝ) : ℂ) * Complex.exp ((alpha : ℂ) * Complex.I)
  rw [hangle]
  simp only [Complex.exp_ofReal_mul_I, Real.cos_sub_pi_div_two,
    Real.sin_sub_pi_div_two, Real.sin_two_mul, Real.cos_two_mul_eq_one_sub]
  push_cast
  ring

/-- The published indices put the half-angle in the principal-argument interval. -/
theorem individualPhase_rootKappa_zero (m ell : ℕ)
    (hell : 1 ≤ ell) (hellm : ell < m) :
    individualPhase (rootKappa m ell) 0 =
      Real.pi * (ell : ℝ) / (2 * (m : ℝ)) := by
  let alpha : ℝ := Real.pi * (ell : ℝ) / (2 * (m : ℝ))
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hellpos : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast (show 0 < ell by omega)
  have helllt : (ell : ℝ) < (m : ℝ) := by exact_mod_cast hellm
  have hden : 0 < 2 * (m : ℝ) := mul_pos (by norm_num) hmpos
  have halpha : 0 < alpha := div_pos (mul_pos Real.pi_pos hellpos) hden
  have halphahalf : alpha < Real.pi / 2 := by
    change Real.pi * (ell : ℝ) / (2 * (m : ℝ)) < Real.pi / 2
    apply (div_lt_iff₀ hden).2
    nlinarith [mul_lt_mul_of_pos_left helllt Real.pi_pos]
  have hsin : 0 < Real.sin alpha :=
    Real.sin_pos_of_pos_of_lt_pi halpha (by linarith [Real.pi_pos])
  change individualPhase (rootKappa m ell) 0 = alpha
  rw [individualPhase, phaseNormalized_zero, rootKappa_add_I]
  change (((2 * Real.sin alpha : ℝ) : ℂ) *
    Complex.exp ((alpha : ℂ) * Complex.I)).arg = alpha
  rw [Complex.arg_real_mul _ (mul_pos (by norm_num) hsin), Complex.exp_mul_I]
  exact Complex.arg_cos_add_sin_mul_I
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-- On positive arguments, this is exactly the sum in manuscript (3). -/
theorem manuscriptPsi_eq_original (m : ℕ) (θ : ℝ)
    (hθ : 0 < θ) (hθπ : θ ≤ Real.pi) :
    manuscriptPsi m θ =
      ∑ ell : Fin (m - 1),
        (1 - stableRootCurve (rootKappa m (ell.val + 1)) θ *
          Complex.exp (-(θ : ℂ) * Complex.I)).arg := by
  unfold manuscriptPsi
  apply Finset.sum_congr rfl
  intro ell _
  exact individualPhase_eq_original _ θ hθ hθπ

/-- The finite sum is smooth at every point of the closed interval. -/
theorem manuscriptPsi_contDiffAt (m : ℕ) (hm : 1 ≤ m)
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi) :
    ContDiffAt ℝ ⊤ (manuscriptPsi m) θ := by
  unfold manuscriptPsi
  apply ContDiffAt.sum
  intro ell _
  apply individualPhase_contDiffAt _ ?_ θ hθ
  exact rootKappa_re_pos m (ell.val + 1) (by omega)
    (by have hell := ell.isLt; omega)

theorem manuscriptEta_contDiffAt (m : ℕ) (hm : 1 ≤ m)
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi) :
    ContDiffAt ℝ ⊤ (manuscriptEta m) θ := by
  exact contDiffAt_id.add (contDiffAt_const.mul (manuscriptPsi_contDiffAt m hm θ hθ))

private lemma sum_fin_add_one_real (N : ℕ) :
    (∑ ell : Fin N, ((ell.val : ℝ) + 1)) = (N : ℝ) * ((N : ℝ) + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    push_cast
    ring

/-- Summing the individual endpoint arguments gives the unwrapped phase. -/
theorem manuscriptPsi_zero (m : ℕ) (hm : 1 ≤ m) :
    manuscriptPsi m 0 = ((m : ℝ) - 1) * Real.pi / 4 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hsum : (∑ ell : Fin (m - 1), ((ell.val : ℝ) + 1)) =
      (m : ℝ) * ((m : ℝ) - 1) / 2 := by
    rw [sum_fin_add_one_real, Nat.cast_sub hm, Nat.cast_one]
    ring
  calc
    manuscriptPsi m 0 =
        ∑ ell : Fin (m - 1), Real.pi * ((ell.val : ℝ) + 1) / (2 * (m : ℝ)) := by
      unfold manuscriptPsi
      apply Finset.sum_congr rfl
      intro ell _
      simpa only [Nat.cast_add, Nat.cast_one] using
        individualPhase_rootKappa_zero m (ell.val + 1) (by omega)
          (by have hell := ell.isLt; omega)
    _ = Real.pi * (∑ ell : Fin (m - 1), ((ell.val : ℝ) + 1)) /
        (2 * (m : ℝ)) := by rw [← Finset.sum_div, ← Finset.mul_sum]
    _ = ((m : ℝ) - 1) * Real.pi / 4 := by
      rw [hsum]
      field_simp [ne_of_gt hmpos] <;> ring

theorem manuscriptEta_zero (m : ℕ) (hm : 1 ≤ m) :
    manuscriptEta m 0 = ((m : ℝ) - 1) * Real.pi / 2 := by
  rw [manuscriptEta, manuscriptPsi_zero m hm]
  ring

#print axioms rootKappa_add_I
#print axioms individualPhase_rootKappa_zero
#print axioms manuscriptPsi_eq_original
#print axioms manuscriptPsi_contDiffAt
#print axioms manuscriptEta_contDiffAt
#print axioms manuscriptPsi_zero
#print axioms manuscriptEta_zero

end MF21Restart
