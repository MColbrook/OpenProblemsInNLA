import MF21Restart.PhaseZero
import MF21Restart.StableRootSymmetry

/-! The upper endpoint phase is zero by pairing individual arguments,
using the actual conjugate-root permutation. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

theorem individualPhase_pi (κ : ℂ) :
    individualPhase κ Real.pi = (1 + stableRootCurve κ Real.pi).arg := by
  rw [individualPhase_eq_original κ Real.pi Real.pi_pos le_rfl]
  simp only [neg_mul, Complex.exp_neg_pi_mul_I, mul_neg_one, sub_neg_eq_add]

theorem one_add_stableRootCurve_pi_re_pos (κ : ℂ) (hκ : 0 < κ.re) :
    0 < (1 + stableRootCurve κ Real.pi).re := by
  have hr := stableRootCurve_norm_lt_one κ hκ Real.pi Real.pi_pos le_rfl
  have hre := Complex.re_le_norm (-stableRootCurve κ Real.pi)
  simp only [Complex.neg_re, norm_neg] at hre
  simp only [Complex.add_re, Complex.one_re]
  linarith

theorem individualPhase_rootKappa_pi_reflect (m ell : ℕ)
    (hell : 1 ≤ ell) (hellm : ell < m) :
    individualPhase (rootKappa m (m - ell)) Real.pi =
      -individualPhase (rootKappa m ell) Real.pi := by
  have hre := one_add_stableRootCurve_pi_re_pos (rootKappa m ell)
    (rootKappa_re_pos m ell hell hellm)
  have hne : (1 + stableRootCurve (rootKappa m ell) Real.pi).arg ≠ Real.pi :=
    ne_of_lt (Complex.arg_lt_pi_iff.mpr (Or.inl hre.le))
  have hconj : 1 + stableRootCurve (rootKappa m (m - ell)) Real.pi =
      (starRingEnd ℂ) (1 + stableRootCurve (rootKappa m ell) Real.pi) := by
    simp only [map_add, map_one, stableRootCurve_rootKappa_conj m ell hell hellm]
  rw [individualPhase_pi, individualPhase_pi, hconj, Complex.arg_conj, if_neg hne]

theorem manuscriptPsi_pi (m : ℕ) (hm : 1 ≤ m) : manuscriptPsi m Real.pi = 0 := by
  have hreverse :
      (∑ ell : Fin (m - 1),
        individualPhase (rootKappa m (ell.rev.val + 1)) Real.pi) =
        manuscriptPsi m Real.pi := by
    simpa only [Fin.revPerm_apply, manuscriptPsi] using
      (Equiv.sum_comp Fin.revPerm
        (fun ell : Fin (m - 1) => individualPhase (rootKappa m (ell.val + 1)) Real.pi))
  have hnegative :
      (∑ ell : Fin (m - 1),
        individualPhase (rootKappa m (ell.rev.val + 1)) Real.pi) =
        -manuscriptPsi m Real.pi := by
    unfold manuscriptPsi
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro ell _
    have hi : ell.rev.val + 1 = m - (ell.val + 1) := by
      rw [Fin.val_rev]
      have := ell.isLt
      omega
    rw [hi]
    exact individualPhase_rootKappa_pi_reflect m (ell.val + 1) (by omega)
      (by have := ell.isLt; omega)
  linarith

theorem manuscriptEta_pi (m : ℕ) (hm : 1 ≤ m) : manuscriptEta m Real.pi = Real.pi := by
  rw [manuscriptEta, manuscriptPsi_pi m hm]
  ring

#print axioms individualPhase_pi
#print axioms individualPhase_rootKappa_pi_reflect
#print axioms manuscriptPsi_pi
#print axioms manuscriptEta_pi

end MF21Restart
