import MF21Restart.DiagonalInterlacing
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fin.Embedding
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
Cauchy interlacing for an actual real Hermitian leading principal block.
The diagonal-form inclusion is constructed from actual orthonormal
eigenbases and literal extension by zero. See the prior statement lock
`HERMITIAN_INTERLACING_STATEMENTS.md`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace

namespace MF21Restart

def hermitianAscendingValue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (i : Fin n) : ℝ :=
  (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
    finrank_euclideanSpace_fin i.rev

private def ascendingEigenbasis {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis
    finrank_euclideanSpace_fin).reindex Fin.revPerm

theorem hermitianAscendingValue_monotone {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    Monotone (hermitianAscendingValue A hA) := by
  intro i j hij
  exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues_antitone
    finrank_euclideanSpace_fin (Fin.rev_le_rev.mpr hij)

theorem hermitianAscendingValue_sorted {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    Multiset.sort (Multiset.ofList (List.ofFn hA.eigenvalues)) =
      List.ofFn (hermitianAscendingValue A hA) := by
  let hT : A.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  let f := hT.eigenvalues finrank_euclideanSpace_fin
  have hcharpoly : A.toEuclideanLin.charpoly = A.charpoly := by
    change (Matrix.toLpLin 2 2 A).charpoly = A.charpoly
    rw [Matrix.toLpLin_eq_toLin, Matrix.charpoly_toLin]
  have hraw : Multiset.ofList (List.ofFn hA.eigenvalues) = A.charpoly.roots := by
    rw [hA.roots_charpoly_eq_eigenvalues]
    simp [Function.comp_def]
  have hdec : A.charpoly.roots = (List.ofFn f : Multiset ℝ) := by
    rw [← hcharpoly, hT.roots_charpoly_eq_eigenvalues finrank_euclideanSpace_fin]
    simp [f, Function.comp_def]
  have hrev : (List.ofFn (hermitianAscendingValue A hA) : Multiset ℝ) =
      (List.ofFn f : Multiset ℝ) := by
    exact Multiset.coe_eq_coe.mpr (Fin.revPerm.ofFn_comp_perm f)
  rw [hraw, hdec, ← hrev, Multiset.coe_sort]
  exact List.mergeSort_eq_self _ (hermitianAscendingValue_monotone A hA).sortedLE_ofFn.pairwise

private theorem ascendingEigenbasis_coordinates {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (ascendingEigenbasis A hA).repr (A.toEuclideanLin x) i =
      hermitianAscendingValue A hA i * (ascendingEigenbasis A hA).repr x i := by
  simp only [ascendingEigenbasis, hermitianAscendingValue,
    OrthonormalBasis.repr_reindex, Fin.revPerm_symm, Fin.revPerm_apply,
    LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply, RCLike.ofReal_real_eq_id, id_eq]

private def hermitianCoordinates {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
  (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.trans
    ((ascendingEigenbasis A hA).repr.toLinearEquiv.trans
      (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)))

private theorem hermitianCoordinates_norm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (x : Fin n → ℝ) :
    (∑ i : Fin n, (hermitianCoordinates A hA x i) ^ 2) =
      ∑ i : Fin n, (x i) ^ 2 := by
  have h := (ascendingEigenbasis A hA).repr.inner_map_map
    (WithLp.toLp 2 x) (WithLp.toLp 2 x)
  change (∑ i : Fin n, hermitianCoordinates A hA x i * hermitianCoordinates A hA x i) =
    ∑ i : Fin n, x i * x i at h
  simpa only [pow_two] using h

private theorem hermitianCoordinates_quadratic {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (x : Fin n → ℝ) :
    (∑ i : Fin n, hermitianAscendingValue A hA i * (hermitianCoordinates A hA x i) ^ 2) =
      ∑ i : Fin n, (A.mulVec x i) * x i := by
  have h := (ascendingEigenbasis A hA).repr.inner_map_map
    (WithLp.toLp 2 x) (A.toEuclideanLin (WithLp.toLp 2 x))
  change (∑ i : Fin n,
    (ascendingEigenbasis A hA).repr (A.toEuclideanLin (WithLp.toLp 2 x)) i *
      hermitianCoordinates A hA x i) = ∑ i : Fin n, (A.mulVec x i) * x i at h
  calc
    _ = ∑ i : Fin n,
        (ascendingEigenbasis A hA).repr (A.toEuclideanLin (WithLp.toLp 2 x)) i *
          hermitianCoordinates A hA x i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [ascendingEigenbasis_coordinates]
      change hermitianAscendingValue A hA i * (hermitianCoordinates A hA x i) ^ 2 =
        (hermitianAscendingValue A hA i * hermitianCoordinates A hA x i) *
          hermitianCoordinates A hA x i
      ring
    _ = _ := h

private theorem sum_mul_initialCoordinateEmbedding
    (n N : ℕ) (hnN : n ≤ N) (f : Fin N → ℝ) (x : Fin n → ℝ) :
    (∑ i : Fin N, f i * initialCoordinateEmbedding n N hnN x i) =
      ∑ i : Fin n, f (Fin.castLE hnN i) * x i := by
  classical
  let e := Fin.castLEEmb hnN
  have hsub : (Finset.univ.map e : Finset (Fin N)) ⊆ Finset.univ := Finset.subset_univ _
  calc
    _ = ∑ i ∈ Finset.univ.map e, f i * initialCoordinateEmbedding n N hnN x i := by
      symm
      apply Finset.sum_subset hsub
      intro i _ hi
      have hout : n ≤ i.val := by
        by_contra hnot
        apply hi
        apply Finset.mem_map.mpr
        refine ⟨⟨i.val, by omega⟩, Finset.mem_univ _, ?_⟩
        exact Fin.ext rfl
      rw [initialCoordinateEmbedding_apply_of_le n N hnN x i hout, mul_zero]
    _ = ∑ i : Fin n, f (Fin.castLE hnN i) * x i := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro i _
      rw [show e i = Fin.castLE hnN i from rfl,
        initialCoordinateEmbedding_apply_castLE]

private theorem initialCoordinateEmbedding_norm
    (n N : ℕ) (hnN : n ≤ N) (x : Fin n → ℝ) :
    (∑ i : Fin N, (initialCoordinateEmbedding n N hnN x i) ^ 2) =
      ∑ i : Fin n, (x i) ^ 2 := by
  simpa only [initialCoordinateEmbedding_apply_castLE, pow_two] using
    sum_mul_initialCoordinateEmbedding n N hnN (initialCoordinateEmbedding n N hnN x) x

private theorem initialCoordinateEmbedding_quadratic
    (n N : ℕ) (hnN : n ≤ N) (B : Matrix (Fin N) (Fin N) ℝ) (x : Fin n → ℝ) :
    (∑ i : Fin N, (B.mulVec (initialCoordinateEmbedding n N hnN x) i) *
        initialCoordinateEmbedding n N hnN x i) =
      ∑ i : Fin n, ((B.submatrix (Fin.castLE hnN) (Fin.castLE hnN)).mulVec x i) * x i := by
  rw [sum_mul_initialCoordinateEmbedding]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change (∑ k : Fin N, B (Fin.castLE hnN i) k * initialCoordinateEmbedding n N hnN x k) =
    ∑ k : Fin n, B (Fin.castLE hnN i) (Fin.castLE hnN k) * x k
  exact sum_mul_initialCoordinateEmbedding n N hnN (B (Fin.castLE hnN i)) x

/-- Actual leading principal-block interlacing, with the required inclusion
constructed from orthonormal eigenbases. No spectral comparison is a premise. -/
theorem hermitian_principal_interlacing
    (n N : ℕ) (hnN : n ≤ N)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hblock : B.submatrix (Fin.castLE hnN) (Fin.castLE hnN) = A) (j : Fin n) :
    hermitianAscendingValue B hB (Fin.castLE hnN j) ≤ hermitianAscendingValue A hA j ∧
      hermitianAscendingValue A hA j ≤
        hermitianAscendingValue B hB ⟨j.val + (N - n), by have := j.isLt; omega⟩ := by
  let ea := hermitianCoordinates A hA
  let eb := hermitianCoordinates B hB
  let E := initialCoordinateEmbedding n N hnN
  let L : (Fin n → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
    eb.toLinearMap.comp (E.comp ea.symm.toLinearMap)
  apply diagonal_isometry_interlacing n N hnN
    (hermitianAscendingValue A hA) (hermitianAscendingValue B hB)
    (hermitianAscendingValue_monotone A hA) (hermitianAscendingValue_monotone B hB) L
    ?_ ?_ j
  · intro x
    change (∑ i : Fin N, (eb (E (ea.symm x)) i) ^ 2) = ∑ i : Fin n, (x i) ^ 2
    calc
      _ = ∑ i : Fin N, (E (ea.symm x) i) ^ 2 :=
        hermitianCoordinates_norm B hB _
      _ = ∑ i : Fin n, (ea.symm x i) ^ 2 := initialCoordinateEmbedding_norm n N hnN _
      _ = ∑ i : Fin n, (x i) ^ 2 := by
        have h := hermitianCoordinates_norm A hA (ea.symm x)
        change (∑ i : Fin n, (ea (ea.symm x) i) ^ 2) = _ at h
        simpa only [LinearEquiv.apply_symm_apply] using h.symm
  · intro x
    change (∑ i : Fin N, hermitianAscendingValue B hB i * (eb (E (ea.symm x)) i) ^ 2) =
      ∑ i : Fin n, hermitianAscendingValue A hA i * (x i) ^ 2
    calc
      _ = ∑ i : Fin N, (B.mulVec (E (ea.symm x)) i) * E (ea.symm x) i :=
        hermitianCoordinates_quadratic B hB _
      _ = ∑ i : Fin n, (A.mulVec (ea.symm x) i) * ea.symm x i := by
        rw [initialCoordinateEmbedding_quadratic n N hnN B, hblock]
      _ = ∑ i : Fin n, hermitianAscendingValue A hA i * (x i) ^ 2 := by
        have h := hermitianCoordinates_quadratic A hA (ea.symm x)
        change (∑ i : Fin n, hermitianAscendingValue A hA i * (ea (ea.symm x) i) ^ 2) = _ at h
        simpa only [LinearEquiv.apply_symm_apply] using h.symm

#print axioms hermitianAscendingValue_monotone
#print axioms hermitianAscendingValue_sorted
#print axioms hermitian_principal_interlacing

end MF21Restart
