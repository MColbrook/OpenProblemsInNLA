import MF21Restart.EigenvalueBridge
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Data.Fintype.Fin
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
Multiplicity in the unchanged sorted real list equals the complex geometric
multiplicity of the actual Toeplitz matrix. The only simplicity premise in
the index corollary is the stated dimension-one premise.

The statement lock is `EIGENVALUE_MULTIPLICITY_STATEMENTS.md`.
-/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

/-- Changing from Euclidean-space coordinates to ordinary function coordinates
restricts to an equivalence of the actual eigenspaces. -/
private theorem finrank_eigenspace_toEuclideanLin
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (lam : ℂ) :
    Module.finrank ℂ (Module.End.eigenspace A.toEuclideanLin lam) =
      Module.finrank ℂ (Module.End.eigenspace A.mulVecLin lam) := by
  let e : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] (Fin n → ℂ) :=
    WithLp.linearEquiv 2 ℂ (Fin n → ℂ)
  have hmap (x : EuclideanSpace ℂ (Fin n)) :
      e (A.toEuclideanLin x) = A.mulVecLin (e x) := rfl
  have heq : Module.End.eigenspace A.toEuclideanLin lam =
      (Module.End.eigenspace A.mulVecLin lam).comap e.toLinearMap := by
    ext x
    rw [Submodule.mem_comap, Module.End.mem_eigenspace_iff,
      Module.End.mem_eigenspace_iff]
    change A.toEuclideanLin x = lam • x ↔ A.mulVecLin (e x) = lam • e x
    constructor
    · intro hx
      calc
        A.mulVecLin (e x) = e (A.toEuclideanLin x) := (hmap x).symm
        _ = e (lam • x) := congrArg e hx
        _ = lam • e x := e.map_smul lam x
    · intro hx
      apply e.injective
      calc
        e (A.toEuclideanLin x) = A.mulVecLin (e x) := hmap x
        _ = lam • e x := hx
        _ = e (lam • x) := (e.map_smul lam x).symm
  rw [heq]
  exact (e.ofSubmodule' (Module.End.eigenspace A.mulVecLin lam)).finrank_eq

/-- Mathlib's Hermitian spectral theorem counts each eigenspace dimension in
the characteristic-root multiset; no algebraic simplicity is assumed. -/
private theorem complex_hermitian_count_roots_eq_finrank_eigenspace
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (lam : ℂ) :
    A.charpoly.roots.count lam =
      Module.finrank ℂ (Module.End.eigenspace A.mulVecLin lam) := by
  classical
  let hT : A.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hcharpoly : A.toEuclideanLin.charpoly = A.charpoly := by
    change (Matrix.toLpLin 2 2 A).charpoly = A.charpoly
    rw [Matrix.toLpLin_eq_toLin, Matrix.charpoly_toLin]
  have hdim : A.toEuclideanLin.charpoly.roots.count lam =
      Module.finrank ℂ (Module.End.eigenspace A.toEuclideanLin lam) := by
    rw [hT.roots_charpoly_eq_eigenvalues finrank_euclideanSpace_fin,
      Multiset.count_map]
    change (Finset.univ.filter (fun i : Fin n =>
      lam = (hT.eigenvalues finrank_euclideanSpace_fin i : ℂ))).card = _
    have hfilter :
        (Finset.univ.filter (fun i : Fin n =>
          lam = (hT.eigenvalues finrank_euclideanSpace_fin i : ℂ))) =
        (Finset.univ.filter (fun i : Fin n =>
          (hT.eigenvalues finrank_euclideanSpace_fin i : ℂ) = lam)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_comm]
    rw [hfilter]
    exact hT.card_filter_eigenvalues_eq finrank_euclideanSpace_fin lam
  rw [hcharpoly] at hdim
  exact hdim.trans (finrank_eigenspace_toEuclideanLin n A lam)

theorem count_orderedEigenvalueList_eq_complex_eigenspace_finrank
    (m n : ℕ) (lam : ℝ) :
    (orderedEigenvalueList m n).count lam =
      Module.finrank ℂ
        (Module.End.eigenspace
          ((toeplitz m n).map Complex.ofReal).mulVecLin (lam : ℂ)) := by
  classical
  have hlist : (orderedEigenvalueList m n : Multiset ℝ) =
      (toeplitz m n).charpoly.roots := by
    rw [(toeplitz_isHermitian m n).roots_charpoly_eq_eigenvalues]
    simp [orderedEigenvalueList, Function.comp_def]
    exact List.mergeSort_perm _ _
  have hA : ((toeplitz m n).map Complex.ofReal).IsHermitian :=
    (toeplitz_isHermitian m n).map Complex.ofReal (by intro x; simp)
  calc
    (orderedEigenvalueList m n).count lam = (toeplitz m n).charpoly.roots.count lam := by
      simpa only [Multiset.coe_count] using
        congrArg (fun s : Multiset ℝ => s.count lam) hlist
    _ = Polynomial.rootMultiplicity lam (toeplitz m n).charpoly :=
      Polynomial.count_roots _
    _ = Polynomial.rootMultiplicity (lam : ℂ)
        ((toeplitz m n).charpoly.map Complex.ofRealHom) :=
      Polynomial.eq_rootMultiplicity_map Complex.ofReal_injective lam
    _ = ((toeplitz m n).map Complex.ofReal).charpoly.roots.count (lam : ℂ) := by
      change Polynomial.rootMultiplicity (Complex.ofRealHom lam)
        ((toeplitz m n).charpoly.map Complex.ofRealHom) =
        ((toeplitz m n).map Complex.ofRealHom).charpoly.roots.count (Complex.ofRealHom lam)
      rw [Matrix.charpoly_map, Polynomial.count_roots]
    _ = _ := complex_hermitian_count_roots_eq_finrank_eigenspace
      n ((toeplitz m n).map Complex.ofReal) hA (lam : ℂ)

/-- Dimension one yields one and only one position in the published one-based
index range. The accessor's values outside that range do not participate. -/
theorem existsUnique_eigenvalue_index_of_complex_eigenspace_finrank_one
    (m n : ℕ) (lam : ℝ)
    (hdim : Module.finrank ℂ
      (Module.End.eigenspace
        ((toeplitz m n).map Complex.ofReal).mulVecLin (lam : ℂ)) = 1) :
    ∃! j : ℕ, 1 ≤ j ∧ j ≤ n ∧ eigenvalue m n j = lam := by
  classical
  have hcard := Fin.card_filter_univ_eq_vector_get_eq_count lam
    (⟨orderedEigenvalueList m n, length_orderedEigenvalueList m n⟩ : List.Vector ℝ n)
  change (Finset.univ.filter (fun i : Fin n => orderedEigenvalue m n i = lam)).card =
    (orderedEigenvalueList m n).count lam at hcard
  rw [count_orderedEigenvalueList_eq_complex_eigenspace_finrank, hdim] at hcard
  obtain ⟨i, hi, hunique⟩ := Finset.card_eq_one_iff_existsUnique.mp hcard
  have hi' : orderedEigenvalue m n i = lam := by simpa only
    [Finset.mem_filter, Finset.mem_univ, true_and] using hi
  refine ⟨i.val + 1, ⟨by omega, by have := i.isLt; omega, ?_⟩, ?_⟩
  · rw [eigenvalue_in_range (by omega) (by have := i.isLt; omega)]
    simpa only [Nat.add_sub_cancel] using hi'
  · intro j hj
    rcases hj with ⟨hj1, hjn, hjvalue⟩
    let k : Fin n := ⟨j - 1, by omega⟩
    have hk : k ∈ Finset.univ.filter (fun a : Fin n => orderedEigenvalue m n a = lam) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [eigenvalue_in_range hj1 hjn] at hjvalue
      exact hjvalue
    have hval := congrArg Fin.val (hunique k hk)
    dsimp [k] at hval
    omega

#print axioms count_orderedEigenvalueList_eq_complex_eigenspace_finrank
#print axioms existsUnique_eigenvalue_index_of_complex_eigenspace_finrank_one

end MF21Restart
