import MF21.CompressionInterlacing
import MF21.BoundarySpectrum
import MF21.Eigenangles

open Matrix
noncomputable section
namespace MF21Audit

/-- A one-dimensional eigenspace contains at most one column of a diagonalizing basis. -/
theorem diagonalization_unique_index {n : ℕ}
    (A U V : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℂ)
    (hVU : V*U = 1) (hAU : A*U = U*diagonal lam)
    (z : ℂ) (hdim : Module.finrank ℂ (Module.End.eigenspace A.mulVecLin z) = 1)
    (i k : Fin n) (hi : lam i = z) (hk : lam k = z) : i = k := by
  let v (j : Fin n) : Fin n → ℂ := U.mulVec (Pi.single j 1)
  have hV (j : Fin n) : V.mulVec (v j) = Pi.single j 1 := by
    dsimp [v]
    rw [Matrix.mulVec_mulVec, hVU, Matrix.one_mulVec]
  have hv0 (j : Fin n) : v j ≠ 0 := by
    intro hz
    have hh := hV j
    rw [hz, Matrix.mulVec_zero] at hh
    have he := congrFun hh j
    simp at he
  have hvEigen (j : Fin n) (hj : lam j = z) :
      v j ∈ Module.End.eigenspace A.mulVecLin z := by
    apply Module.End.mem_eigenspace_iff.mpr
    change A.mulVec (U.mulVec (Pi.single j 1)) = z • U.mulVec (Pi.single j 1)
    rw [Matrix.mulVec_mulVec, hAU, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul]
    congr 1
    ext l
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal, Pi.single_apply]
    split_ifs <;> simp_all
  let vi : Module.End.eigenspace A.mulVecLin z := ⟨v i, hvEigen i hi⟩
  let vk : Module.End.eigenspace A.mulVecLin z := ⟨v k, hvEigen k hk⟩
  have hvi : vi ≠ 0 := by
    intro hh
    exact hv0 i (congrArg Subtype.val hh)
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' vi hvi).mp hdim vk
  have he : a • v i = v k := congrArg Subtype.val ha
  have hc := congrArg (fun w ↦ V.mulVec w) he
  rw [Matrix.mulVec_smul, hV, hV] at hc
  by_contra hik
  have hh := congrFun hc k
  simp [Ne.symm hik] at hh

end MF21Audit
namespace MF21Challenge

/-- Complexification preserves the diagonalizing basis and its indexed eigenvalues. -/
theorem unique_index_of_complex_eigenspace_finrank_one (m n : ℕ) (z : ℝ)
    (hdim : Module.finrank ℂ (Module.End.eigenspace (MF21Boundary.toeplitz m n).mulVecLin
      (z : ℂ)) = 1) (i k : Fin n)
    (hi : eigenvalue m n i = z) (hk : eigenvalue m n k = z) : i = k := by
  obtain ⟨U, hU, hU', hD⟩ := exists_ordered_diagonalization (toeplitz_isHermitian m n)
  let UC := U.map Complex.ofRealHom
  let VC := U.transpose.map Complex.ofRealHom
  have hVU : VC*UC = 1 := by
    dsimp [VC, UC]
    rw [← Matrix.map_mul, hU]
    exact Matrix.map_one _ (by simp) (by simp)
  have hAUreal : toeplitz m n*U = U*diagonal (descendingEigenvalue (toeplitz_isHermitian m n)) := by
    rw [← hD]
    calc
      toeplitz m n*U = (U*U.transpose)*(toeplitz m n*U) := by rw [hU', Matrix.one_mul]
      _ = U*(U.transpose*toeplitz m n*U) := by simp only [Matrix.mul_assoc]
  have hAU : MF21Boundary.toeplitz m n*UC =
      UC*diagonal (fun j ↦ (descendingEigenvalue (toeplitz_isHermitian m n) j : ℂ)) := by
    have hh := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ ↦ A.map Complex.ofRealHom) hAUreal
    rw [Matrix.map_mul, Matrix.map_mul] at hh
    convert hh using 1
    · rfl
    · congr 1
      ext a b
      by_cases hab : a = b <;> simp [hab]
  have he := MF21Audit.diagonalization_unique_index (MF21Boundary.toeplitz m n) UC VC
    (fun j ↦ (descendingEigenvalue (toeplitz_isHermitian m n) j : ℂ)) hVU hAU
    (z : ℂ) hdim i.rev k.rev (by exact_mod_cast hi) (by exact_mod_cast hk)
  exact Fin.rev_injective he

theorem unique_eigenangle_index_of_complex_eigenspace_finrank_one
    (m n : ℕ) (hm : 0 < m) (theta : ℝ)
    (hdim : Module.finrank ℂ (Module.End.eigenspace (MF21Boundary.toeplitz m n).mulVecLin
      (symbol m theta : ℂ)) = 1) (i k : Fin n)
    (hi : eigenangle m n hm i = theta) (hk : eigenangle m n hm k = theta) : i = k := by
  apply unique_index_of_complex_eigenspace_finrank_one m n (symbol m theta) hdim i k
  · rw [← hi, symbol_eigenangle]
  · rw [← hk, symbol_eigenangle]

end MF21Challenge

#print axioms MF21Audit.diagonalization_unique_index
#print axioms MF21Challenge.unique_index_of_complex_eigenspace_finrank_one
#print axioms MF21Challenge.unique_eigenangle_index_of_complex_eigenspace_finrank_one
