import MF21.BoundaryBlockForm
import MF21.BulkTotalPhase
import MF21.BulkSlopes

/-! Conjugation of the boundary determinant, including its permutation sign. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace MF21Normalization

def conjugationPermutation (m : ℕ) (i₀ : Fin m) (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin m ⊕ Fin m) :=
  (τ.sumCongr τ).trans (Equiv.swap (Sum.inl i₀) (Sum.inr i₀))

theorem conjugationPermutation_sign (m : ℕ) (i₀ : Fin m) (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (conjugationPermutation m i₀ τ) = -1 := by
  rw [conjugationPermutation, Equiv.Perm.sign_trans, Equiv.Perm.sign_sumCongr,
    Equiv.Perm.sign_swap (by simp)]
  have hs : Equiv.Perm.sign τ * Equiv.Perm.sign τ = 1 := Int.units_mul_self _
  rw [hs, mul_one]

/-- Conjugating a root family with a negative-sign permutation negates its
exact boundary determinant. -/
theorem blockPower_conj_det (m p : ℕ) (z : Fin m ⊕ Fin m → ℂ)
    (σ : Equiv.Perm (Fin m ⊕ Fin m)) (hs : Equiv.Perm.sign σ = -1)
    (hz : ∀ j, (starRingEnd ℂ) (z j) = z (σ j)) :
    (starRingEnd ℂ) ((blockPower m z (fun j => z j^p)).det) =
      -(blockPower m z (fun j => z j^p)).det := by
  rw [RingHom.map_det]
  have he : (starRingEnd ℂ).mapMatrix (blockPower m z (fun j => z j^p)) =
      (blockPower m z (fun j => z j^p)).submatrix id σ := by
    ext i j
    cases i <;> simp [blockPower, RingHom.mapMatrix_apply, Matrix.submatrix_apply, hz]
  rw [he, Matrix.det_permute', hs]
  simp

/-- Duplicating any stable-root permutation cancels its sign; only the
transposition of the two unit roots contributes a minus sign. -/
theorem blockPower_conj_det_of_duplicate (m p : ℕ) (i₀ : Fin m)
    (τ : Equiv.Perm (Fin m)) (z : Fin m ⊕ Fin m → ℂ)
    (hz : ∀ j, (starRingEnd ℂ) (z j) = z (conjugationPermutation m i₀ τ j)) :
    (starRingEnd ℂ) ((blockPower m z (fun j => z j^p)).det) =
      -(blockPower m z (fun j => z j^p)).det :=
  blockPower_conj_det m p z _ (conjugationPermutation_sign m i₀ τ) hz

end MF21Normalization
#print axioms MF21Normalization.blockPower_conj_det_of_duplicate

namespace MF21Bulk

theorem omega_neg (m : ℕ) [NeZero m] (j : Fin m) :
    omega m (-j) = (starRingEnd ℂ) (omega m j) := by
  by_cases hj : j=0
  · simp [hj, omega]
  · rw [← Complex.inv_eq_conj (omega_norm m j)]
    apply eq_inv_of_mul_eq_one_left
    rw [omega, omega, ← pow_add]
    have he : (-j).val+j.val=m := by
      rw [Fin.val_neg, if_neg hj]
      omega
    rw [he, (Complex.isPrimitiveRoot_exp m (NeZero.ne m)).pow_eq_one]

theorem baseRoot_neg_conj (m : ℕ) [NeZero m] (theta : ℝ)
    (ht : theta ∈ Set.Ioc 0 Real.pi) (j : Fin m) (hj : j≠0) :
    baseRoot m theta (-j) = (starRingEnd ℂ) (baseRoot m theta j) := by
  have hm : 0<m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hv : j.val ≠ 0 := by intro he; exact hj (Fin.ext he)
  have hn : (-j).val ≠ 0 := by
    intro he
    have h : -j=0 := Fin.ext he
    exact hj (neg_eq_zero.mp h)
  rw [baseRoot, if_neg hn, baseRoot, if_neg hv, omega_neg,
    stableRoot_conj _ _ (spectralBase_pos_of_mem theta ht) (omega_norm m j)
      (omega_ne_one m hm j hv)]

/-- The actual reciprocal root family is conjugated by a duplicated index
negation followed by the transposition of the unit roots. -/
theorem blockRootFamily_conj (m : ℕ) [NeZero m] (theta : ℝ)
    (ht : theta ∈ Set.Ioc 0 Real.pi) (j : Fin m ⊕ Fin m) :
    (starRingEnd ℂ) (blockRootFamily m theta j) =
      blockRootFamily m theta
        (MF21Normalization.conjugationPermutation m 0 (Equiv.neg (Fin m)) j) := by
  cases j with
  | inl j =>
    by_cases hj : j=0
    · subst j
      simp [MF21Normalization.conjugationPermutation, blockRootFamily, baseRoot,
        ← Complex.inv_eq_conj (unitRoot_norm theta)]
    · have hn : -j≠0 := neg_ne_zero.mpr hj
      have he := baseRoot_neg_conj m theta ht j hj
      simp [MF21Normalization.conjugationPermutation, blockRootFamily,
        Equiv.swap_apply_of_ne_of_ne (show (Sum.inl (-j) : Fin m ⊕ Fin m) ≠ Sum.inl 0 by simpa using hn)
          (show (Sum.inl (-j) : Fin m ⊕ Fin m) ≠ Sum.inr 0 by simp), he]
  | inr j =>
    by_cases hj : j=0
    · subst j
      simp [MF21Normalization.conjugationPermutation, blockRootFamily, baseRoot,
        ← Complex.inv_eq_conj (unitRoot_norm theta)]
    · have hn : -j≠0 := neg_ne_zero.mpr hj
      have he := baseRoot_neg_conj m theta ht j hj
      simp [MF21Normalization.conjugationPermutation, blockRootFamily,
        Equiv.swap_apply_of_ne_of_ne (show (Sum.inr (-j) : Fin m ⊕ Fin m) ≠ Sum.inl 0 by simp)
          (show (Sum.inr (-j) : Fin m ⊕ Fin m) ≠ Sum.inr 0 by simpa using hn), he]

end MF21Bulk

namespace MF21ActualBoundary

theorem determinant_conj (m n : ℕ) (hm : 0<m) (theta : ℝ)
    (ht : theta ∈ Set.Ioc 0 Real.pi) :
    (starRingEnd ℂ) (determinant m n theta) = -determinant m n theta := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  rw [determinant_block_form]
  have he : blockRoots m theta = MF21Bulk.blockRootFamily m theta := by
    funext j
    cases j <;> simp [MF21Bulk.blockRootFamily]
  rw [he]
  exact MF21Normalization.blockPower_conj_det_of_duplicate m (n+m) 0 (Equiv.neg (Fin m))
    _ (MF21Bulk.blockRootFamily_conj m theta ht)


/-- At pi the two unit-root columns coincide, producing the artificial
boundary zero used in the endpoint exclusion argument. -/
theorem determinant_pi (m n : ℕ) (hm : 0<m) : determinant m n Real.pi = 0 := by
  let i₀ : Fin m := ⟨0,hm⟩
  rw [determinant_block_form]
  apply Matrix.det_zero_of_column_eq (i := Sum.inl i₀) (j := Sum.inr i₀) (by simp)
  intro k
  have hz : blockRoots m Real.pi (Sum.inl i₀) = blockRoots m Real.pi (Sum.inr i₀) := by
    simp [i₀, MF21Bulk.baseRoot, MF21Bulk.unitRoot, Complex.exp_pi_mul_I]
  cases k <;> simp only [MF21Normalization.blockPower, Sum.elim_inl, Sum.elim_inr, hz]

end MF21ActualBoundary
#print axioms MF21ActualBoundary.determinant_conj

#print axioms MF21ActualBoundary.determinant_pi
