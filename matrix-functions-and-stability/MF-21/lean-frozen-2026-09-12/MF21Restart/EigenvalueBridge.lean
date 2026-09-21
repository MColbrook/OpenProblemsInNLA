import MF21Restart.Definitions

/-! The one-based manuscript accessor enumerates exactly the actual
characteristic roots; no out-of-range totalized value is counted. -/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

lemma length_orderedEigenvalueList (m n : ℕ) :
    (orderedEigenvalueList m n).length = n := by
  simp [orderedEigenvalueList]

theorem eigenvalue_index_iff_mem_orderedList (m n : ℕ) (lam : ℝ) :
    (∃ j : ℕ, 1 ≤ j ∧ j ≤ n ∧ eigenvalue m n j = lam) ↔
      lam ∈ orderedEigenvalueList m n := by
  constructor
  · rintro ⟨j, hj, hjn, hvalue⟩
    rw [eigenvalue_in_range hj hjn] at hvalue
    rw [← hvalue]
    exact List.get_mem _ _
  · intro hmem
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmem
    have hin : i.val < n := by
      simpa only [length_orderedEigenvalueList] using i.isLt
    refine ⟨i.val + 1, by omega, by omega, ?_⟩
    rw [eigenvalue_in_range (by omega) (by omega)]
    simpa only [orderedEigenvalue, Nat.add_sub_cancel] using hi

theorem eigenvalue_index_iff_charpoly_root (m n : ℕ) (lam : ℝ) :
    (∃ j : ℕ, 1 ≤ j ∧ j ≤ n ∧ eigenvalue m n j = lam) ↔
      (toeplitz m n).charpoly.IsRoot lam := by
  rw [eigenvalue_index_iff_mem_orderedList,
    ← Polynomial.mem_roots (Matrix.charpoly_monic (toeplitz m n)).ne_zero,
    (toeplitz_isHermitian m n).roots_charpoly_eq_eigenvalues]
  simp [orderedEigenvalueList, Function.comp_def]

#print axioms eigenvalue_index_iff_mem_orderedList
#print axioms eigenvalue_index_iff_charpoly_root

end MF21Restart
