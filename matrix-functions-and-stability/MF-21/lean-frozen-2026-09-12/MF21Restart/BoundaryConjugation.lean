import MF21Restart.ConcreteBoundary
import Mathlib.Data.Fin.Rev
import Mathlib.GroupTheory.Perm.Sign

set_option autoImplicit false
noncomputable section

namespace MF21Restart

def rootBlockEquiv (m : ℕ) (hm : 1 ≤ m) :
    ((Fin (m - 1) ⊕ Fin 2) ⊕ Fin (m - 1)) ≃ Fin (2 * m) :=
  ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin (m - 1)))).trans
    finSumFinEquiv).trans (finCongr (by omega))

def rootBlockConjugation (m : ℕ) :
    Equiv.Perm ((Fin (m - 1) ⊕ Fin 2) ⊕ Fin (m - 1)) :=
  Equiv.sumCongr (Equiv.sumCongr Fin.revPerm (Equiv.swap (0 : Fin 2) 1)) Fin.revPerm

def rootConjugationPerm (m : ℕ) (hm : 1 ≤ m) : Equiv.Perm (Fin (2 * m)) :=
  ((rootBlockEquiv m hm).symm.trans (rootBlockConjugation m)).trans (rootBlockEquiv m hm)

theorem rootConjugationPerm_sign (m : ℕ) (hm : 1 ≤ m) :
    Equiv.Perm.sign (rootConjugationPerm m hm) = -1 := by
  rw [rootConjugationPerm, Equiv.Perm.sign_symm_trans_trans, rootBlockConjugation,
    Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_sumCongr,
    Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1)]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m - 1))))
      with h | h <;> simp [h]

private theorem roots_rootBlock_stable (m : ℕ) (hm : 1 ≤ m) (θ : ℝ)
    (i : Fin (m - 1)) :
    characteristicRoots m θ (rootBlockEquiv m hm (Sum.inl (Sum.inl i))) =
      stableRootCurve (rootKappa m (i.val + 1)) θ := by
  rw [characteristicRoots_stable m θ _ (show
    (rootBlockEquiv m hm (Sum.inl (Sum.inl i))).val < m - 1 from i.isLt)]
  rfl

private theorem roots_rootBlock_exterior (m : ℕ) (hm : 1 ≤ m) (θ : ℝ)
    (i : Fin (m - 1)) :
    characteristicRoots m θ (rootBlockEquiv m hm (Sum.inr i)) =
      (stableRootCurve (rootKappa m (i.val + 1)) θ)⁻¹ := by
  have hv : (rootBlockEquiv m hm (Sum.inr i)).val = m - 1 + 2 + i.val := rfl
  rw [characteristicRoots_exterior m θ _ (by rw [hv]; omega), hv,
    show m - 1 + 2 + i.val - m = i.val + 1 by omega]

private theorem roots_rootBlock_unit (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) :
    characteristicRoots m θ (rootBlockEquiv m hm (Sum.inl (Sum.inr 0))) =
      oscillatoryRoot θ := by
  apply characteristicRoots_unit
  rfl

private theorem roots_rootBlock_unit_inv (m : ℕ) (hm : 2 ≤ m) (θ : ℝ) :
    characteristicRoots m θ (rootBlockEquiv m (by omega) (Sum.inl (Sum.inr 1))) =
      (oscillatoryRoot θ)⁻¹ := by
  apply characteristicRoots_unit_inv m hm
  change m - 1 + 1 = m
  omega

theorem oscillatoryRoot_conj (θ : ℝ) :
    (starRingEnd ℂ) (oscillatoryRoot θ) = (oscillatoryRoot θ)⁻¹ := by
  rw [oscillatoryRoot, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, Complex.exp_neg]

theorem characteristicRoots_conj (m : ℕ) (hm : 2 ≤ m) (θ : ℝ)
    (i : Fin (2 * m)) :
    (starRingEnd ℂ) (characteristicRoots m θ i) =
      characteristicRoots m θ (rootConjugationPerm m (by omega) i) := by
  have hm1 : 1 ≤ m := by omega
  have hblock : ∀ b : ((Fin (m - 1) ⊕ Fin 2) ⊕ Fin (m - 1)),
      (starRingEnd ℂ) (characteristicRoots m θ (rootBlockEquiv m hm1 b)) =
        characteristicRoots m θ (rootBlockEquiv m hm1 (rootBlockConjugation m b)) := by
    rintro ((j | j) | j)
    · change (starRingEnd ℂ) (characteristicRoots m θ (rootBlockEquiv m hm1 (Sum.inl (Sum.inl j)))) =
        characteristicRoots m θ (rootBlockEquiv m hm1 (Sum.inl (Sum.inl j.rev)))
      rw [roots_rootBlock_stable, roots_rootBlock_stable,
        stableRootCurve_rootKappa_conj m (j.val + 1) (by omega) (by have := j.isLt; omega)]
      have hr : m - (j.val + 1) = j.rev.val + 1 := by
        rw [Fin.val_rev]
        have := j.isLt
        omega
      rw [hr]
    · fin_cases j
      · change (starRingEnd ℂ) (characteristicRoots m θ
          (rootBlockEquiv m hm1 (Sum.inl (Sum.inr (0 : Fin 2))))) =
            characteristicRoots m θ (rootBlockEquiv m hm1 (Sum.inl (Sum.inr (1 : Fin 2))))
        rw [roots_rootBlock_unit, roots_rootBlock_unit_inv m hm, oscillatoryRoot_conj]
      · change (starRingEnd ℂ) (characteristicRoots m θ
          (rootBlockEquiv m hm1 (Sum.inl (Sum.inr (1 : Fin 2))))) =
            characteristicRoots m θ (rootBlockEquiv m hm1 (Sum.inl (Sum.inr (0 : Fin 2))))
        rw [roots_rootBlock_unit_inv m hm, roots_rootBlock_unit, map_inv₀,
          oscillatoryRoot_conj, inv_inv]
    · change (starRingEnd ℂ) (characteristicRoots m θ (rootBlockEquiv m hm1 (Sum.inr j))) =
        characteristicRoots m θ (rootBlockEquiv m hm1 (Sum.inr j.rev))
      rw [roots_rootBlock_exterior, roots_rootBlock_exterior, map_inv₀,
        stableRootCurve_rootKappa_conj m (j.val + 1) (by omega) (by have := j.isLt; omega)]
      have hr : m - (j.val + 1) = j.rev.val + 1 := by
        rw [Fin.val_rev]
        have := j.isLt
        omega
      rw [hr]
  simpa only [rootConjugationPerm, Equiv.trans_apply, Equiv.apply_symm_apply] using
    hblock ((rootBlockEquiv m hm1).symm i)

theorem manuscriptBoundaryDeterminant_conj (m n : ℕ) (hm : 2 ≤ m) (θ : ℝ) :
    (starRingEnd ℂ) (manuscriptBoundaryDeterminant m n θ) =
      -manuscriptBoundaryDeterminant m n θ := by
  let B := boundaryMatrix m n (characteristicRoots m θ)
  have hmap : B.map (starRingEnd ℂ) = B.submatrix id (rootConjugationPerm m (by omega)) := by
    ext row col
    by_cases hr : row.val < m <;>
      simp [B, Matrix.map_apply, Matrix.submatrix_apply, boundaryMatrix,
        hr, map_pow, characteristicRoots_conj m hm]
  change (starRingEnd ℂ) B.det = -B.det
  rw [RingHom.map_det]
  change (B.map (starRingEnd ℂ)).det = -B.det
  rw [hmap, Matrix.det_permute', rootConjugationPerm_sign]
  simp

theorem manuscriptBoundaryDeterminant_re_eq_zero (m n : ℕ) (hm : 2 ≤ m) (θ : ℝ) :
    (manuscriptBoundaryDeterminant m n θ).re = 0 := by
  have h := congrArg Complex.re (manuscriptBoundaryDeterminant_conj m n hm θ)
  simp only [Complex.conj_re, Complex.neg_re] at h
  linarith

#print axioms rootConjugationPerm_sign
#print axioms characteristicRoots_conj
#print axioms manuscriptBoundaryDeterminant_conj
#print axioms manuscriptBoundaryDeterminant_re_eq_zero

end MF21Restart
