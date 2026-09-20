import MF21.BoundaryDeterminant

/-! The boundary determinant detects the exact sorted real eigenvalues from Challenge. -/
noncomputable section
open scoped BigOperators
open Matrix Polynomial
set_option backward.isDefEq.respectTransparency.types false
namespace MF21Boundary

theorem exists_eigenvector_iff_mem_spectrum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (lam : ℂ) :
    (∃ v : Fin n → ℂ, v ≠ 0 ∧ A.mulVec v = lam • v) ↔ lam ∈ spectrum ℂ A := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    have he : Module.End.HasEigenvalue A.mulVecLin lam :=
      Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr hv, hv0⟩
    have hs := Module.End.HasEigenvalue.mem_spectrum he
    simpa only [← Matrix.toLin'_apply', Matrix.spectrum_toLin'] using hs
  · intro hs
    have hs' : lam ∈ spectrum ℂ A.mulVecLin := by
      simpa only [← Matrix.toLin'_apply', Matrix.spectrum_toLin'] using hs
    obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hs').exists_hasEigenvector
    exact ⟨v, hv.2, Module.End.mem_eigenspace_iff.mp hv.1⟩

theorem complex_spectrum_iff_real_charpoly_root (m n : ℕ) (lam : ℝ) :
    (lam : ℂ) ∈ spectrum ℂ (toeplitz m n) ↔
      (MF21Challenge.toeplitz m n).charpoly.IsRoot lam := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
  change ((MF21Challenge.toeplitz m n).map Complex.ofRealHom).charpoly.IsRoot
    (Complex.ofRealHom lam) ↔ _
  rw [Matrix.charpoly_map, Polynomial.isRoot_map_iff Complex.ofReal_injective]

theorem real_charpoly_root_iff_sorted_eigenvalue (m n : ℕ) (lam : ℝ) :
    (MF21Challenge.toeplitz m n).charpoly.IsRoot lam ↔
      ∃ j : Fin n, MF21Challenge.eigenvalue m n j = lam := by
  have hne : (MF21Challenge.toeplitz m n).charpoly ≠ 0 := Matrix.charpoly_monic _ |>.ne_zero
  rw [← Polynomial.mem_roots hne,
    (MF21Challenge.toeplitz_isHermitian m n).roots_charpoly_eq_eigenvalues₀]
  constructor
  · intro h
    obtain ⟨i, hi, he⟩ := Multiset.mem_map.mp h
    refine ⟨(Fin.cast (Fintype.card_fin n) i).rev, ?_⟩
    simpa [MF21Challenge.eigenvalue] using he
  · rintro ⟨j, hj⟩
    apply Multiset.mem_map.mpr
    refine ⟨Fin.cast (Fintype.card_fin n).symm j.rev, ?_, ?_⟩
    · simp
    · simpa [MF21Challenge.eigenvalue] using hj

/-- Complexifying the real Toeplitz matrix does not introduce spurious real eigenvalues. -/
theorem complex_eigenvector_iff_sorted_eigenvalue (m n : ℕ) (lam : ℝ) :
    (∃ v : Fin n → ℂ, v ≠ 0 ∧ (toeplitz m n).mulVec v = (lam : ℂ) • v) ↔
      ∃ j : Fin n, MF21Challenge.eigenvalue m n j = lam := by
  rw [exists_eigenvector_iff_mem_spectrum,
    complex_spectrum_iff_real_charpoly_root, real_charpoly_root_iff_sorted_eigenvalue]

/-- Exact sorted-spectrum interpretation of the finite ghost determinant. -/
theorem sorted_eigenvalue_iff_boundary_det_zero (m n : ℕ) (hm : 0 < m) (lam : ℝ)
    (roots : Fin (2 * m) → ℂ) (hinj : Function.Injective roots)
    (hr : ∀ j, (recurrence m (lam : ℂ)).charPoly.IsRoot (roots j)) :
    (∃ j : Fin n, MF21Challenge.eigenvalue m n j = lam) ↔
      (boundaryMatrix m n roots).det = 0 := by
  rw [← complex_eigenvector_iff_sorted_eigenvalue]
  exact eigenvector_iff_boundary_det_zero m n hm (lam : ℂ) roots hinj hr

end MF21Boundary
#print axioms MF21Boundary.complex_eigenvector_iff_sorted_eigenvalue
#print axioms MF21Boundary.sorted_eigenvalue_iff_boundary_det_zero
