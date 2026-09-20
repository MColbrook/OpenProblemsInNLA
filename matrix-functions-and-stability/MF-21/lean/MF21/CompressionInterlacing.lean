import MF21.SpectralTrace

/-! Finite-dimensional compression interlacing, proved by finding a nonzero
vector in a dimension-forced kernel. No minmax theorem is assumed. -/

open Matrix Finset
noncomputable section
namespace MF21Audit

def prefixLinear (r n : ℕ) : (Fin r → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun x i := if hi : i.val < r then x ⟨i.val, hi⟩ else 0
  map_add' x y := by ext i; dsimp; split_ifs <;> simp
  map_smul' c x := by ext i; dsimp; split_ifs <;> simp

theorem prefixLinear_injective {r n : ℕ} (hr : r ≤ n) :
    Function.Injective (prefixLinear r n) := by
  intro x y h
  funext j
  have hj := congrFun h (⟨j.val, j.isLt.trans_le hr⟩ : Fin n)
  simpa [prefixLinear, j.isLt] using hj

theorem sum_sq_pos_of_ne_zero {n : ℕ} {x : Fin n → ℝ} (hx : x ≠ 0) :
    0 < ∑ i, (x i)^2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  exact sum_pos' (fun _ _ ↦ sq_nonneg _) ⟨i, mem_univ _, sq_pos_of_ne_zero hi⟩

/-- Compression cannot increase any eigenvalue when both spectra are listed
in decreasing order. This coordinate form is independent of the choice of
orthonormal eigenbases. -/
theorem diagonal_compression_antitone_le {n N : ℕ}
    (lam : Fin N → ℝ) (μ : Fin n → ℝ)
    (W : (Fin n → ℝ) →ₗ[ℝ] (Fin N → ℝ))
    (hlam : Antitone lam) (hμ : Antitone μ)
    (hnorm : ∀ x, ∑ i, (W x i)^2 = ∑ j, (x j)^2)
    (hquad : ∀ x, ∑ i, lam i * (W x i)^2 = ∑ j, μ j * (x j)^2)
    (k : ℕ) (hkn : k < n) (hkN : k < N) :
    μ ⟨k, hkn⟩ ≤ lam ⟨k, hkN⟩ := by
  let P := prefixLinear (k + 1) n
  let R : (Fin N → ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
    LinearMap.pi (fun j ↦ LinearMap.proj (⟨j.val, j.isLt.trans hkN⟩ : Fin N))
  let L := R.comp (W.comp P)
  have hdim : Module.finrank ℝ (Fin k → ℝ) < Module.finrank ℝ (Fin (k + 1) → ℝ) := by
    simp
  obtain ⟨c, hc, hcne⟩ := (Submodule.ne_bot_iff L.ker).mp
    (LinearMap.ker_ne_bot_of_finrank_lt hdim)
  let x := P c
  have hxne : x ≠ 0 := by
    intro h
    apply hcne
    apply prefixLinear_injective (by omega : k + 1 ≤ n)
    simpa only [map_zero] using h
  have hzero (i : Fin N) (hi : i.val < k) : W x i = 0 := by
    have hz := congrFun (LinearMap.mem_ker.mp hc) (⟨i.val, hi⟩ : Fin k)
    simpa only [L, R, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply, x,
      Pi.zero_apply, Fin.eta] using hz
  have hxzero (j : Fin n) (hj : k < j.val) : x j = 0 := by
    simp only [x, P, prefixLinear, LinearMap.coe_mk, AddHom.coe_mk, not_lt.mpr (by omega : k + 1 ≤ j.val),
      dite_false]
  have hupper : ∑ i, lam i * (W x i)^2 ≤ lam ⟨k, hkN⟩ * ∑ i, (W x i)^2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro i _
    by_cases hi : i.val < k
    · simp [hzero i hi]
    · exact mul_le_mul_of_nonneg_right (hlam (show (⟨k, hkN⟩ : Fin N) ≤ i from not_lt.mp hi))
        (sq_nonneg _)
  have hlower : μ ⟨k, hkn⟩ * ∑ j, (x j)^2 ≤ ∑ j, μ j * (x j)^2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro j _
    by_cases hj : k < j.val
    · simp [hxzero j hj]
    · exact mul_le_mul_of_nonneg_right (hμ (show j ≤ (⟨k, hkn⟩ : Fin n) from not_lt.mp hj))
        (sq_nonneg _)
  rw [hquad, hnorm] at hupper
  exact (mul_le_mul_iff_left₀ (sum_sq_pos_of_ne_zero hxne)).mp (hlower.trans hupper)

def reverseLinear (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun x i := x i.rev
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem sum_rev {n : ℕ} (f : Fin n → ℝ) : ∑ i : Fin n, f i.rev = ∑ i, f i := by
  simpa only [Fin.revPerm_apply] using Equiv.sum_comp Fin.revPerm f

/-- The second compression bound. The codimension shift is explicit. -/
theorem diagonal_compression_antitone_ge {n N : ℕ}
    (lam : Fin N → ℝ) (μ : Fin n → ℝ)
    (W : (Fin n → ℝ) →ₗ[ℝ] (Fin N → ℝ))
    (hlam : Antitone lam) (hμ : Antitone μ) (hnN : n ≤ N)
    (hnorm : ∀ x, ∑ i, (W x i)^2 = ∑ j, (x j)^2)
    (hquad : ∀ x, ∑ i, lam i * (W x i)^2 = ∑ j, μ j * (x j)^2)
    (k : ℕ) (hkn : k < n) :
    lam ⟨N - n + k, by omega⟩ ≤ μ ⟨k, hkn⟩ := by
  let lam' : Fin N → ℝ := fun i ↦ -lam i.rev
  let μ' : Fin n → ℝ := fun j ↦ -μ j.rev
  let W' := (reverseLinear N).comp (W.comp (reverseLinear n))
  have hlam' : Antitone lam' := fun i j hij ↦
    neg_le_neg (hlam (Fin.rev_le_rev.mpr hij))
  have hμ' : Antitone μ' := fun i j hij ↦
    neg_le_neg (hμ (Fin.rev_le_rev.mpr hij))
  have hnorm' (x : Fin n → ℝ) : ∑ i, (W' x i)^2 = ∑ j, (x j)^2 := by
    change (∑ i : Fin N, (W (reverseLinear n x) i.rev)^2) = _
    rw [sum_rev (fun i ↦ (W (reverseLinear n x) i)^2), hnorm]
    exact sum_rev (fun j ↦ (x j)^2)
  have hquad' (x : Fin n → ℝ) :
      ∑ i, lam' i * (W' x i)^2 = ∑ j, μ' j * (x j)^2 := by
    change (∑ i : Fin N, -lam i.rev * (W (reverseLinear n x) i.rev)^2) =
      ∑ j : Fin n, -μ j.rev * (x j)^2
    simp only [neg_mul, sum_neg_distrib]
    rw [sum_rev (fun i ↦ lam i * (W (reverseLinear n x) i)^2), hquad]
    apply congrArg Neg.neg
    have h := sum_rev (fun j ↦ μ j * (x j.rev)^2)
    simpa only [Fin.rev_rev, reverseLinear, LinearMap.coe_mk, AddHom.coe_mk] using h.symm
  let j : Fin n := ⟨k, hkn⟩
  have hjN : j.rev.val < N := j.rev.isLt.trans_le hnN
  have h := diagonal_compression_antitone_le lam' μ' W' hlam' hμ'
    hnorm' hquad' j.rev.val j.rev.isLt hjN
  have hrev : (⟨j.rev.val, hjN⟩ : Fin N).rev = ⟨N - n + k, by omega⟩ := by
    apply Fin.ext
    simp only [Fin.val_rev, j]
    omega
  change -μ (⟨j.rev.val, j.rev.isLt⟩ : Fin n).rev ≤
    -lam (⟨j.rev.val, hjN⟩ : Fin N).rev at h
  simpa only [Fin.eta, Fin.rev_rev, hrev, neg_le_neg_iff, j] using h

end MF21Audit

namespace MF21Challenge

def descendingEigenvalue {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (j : Fin n) : ℝ :=
  hA.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm j)

theorem descendingEigenvalue_antitone {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) : Antitone (descendingEigenvalue hA) := by
  intro i j hij
  exact hA.eigenvalues₀_antitone hij

theorem exists_ordered_diagonalization {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ,
      Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧ Uᵀ * A * U = diagonal (descendingEigenvalue hA) := by
  let U₀ : Matrix (Fin n) (Fin n) ℝ := hA.eigenvectorUnitary
  let e : Fin n ≃ Fin n := (Fin.castOrderIso (Fintype.card_fin n).symm).toEquiv.trans
    (Fintype.equivOfCardEq (Fintype.card_fin _))
  have hU₀ : U₀ᵀ * U₀ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hU₀' : U₀ * U₀ᵀ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      Unitary.coe_star] using Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hD₀ : U₀ᵀ * A * U₀ = diagonal hA.eigenvalues := by
    simpa only [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def,
      RCLike.ofReal_real_eq_id, id_eq] using hA.conjStarAlgAut_star_eigenvectorUnitary
  refine ⟨U₀.submatrix id e, ?_, ?_, ?_⟩
  · change U₀ᵀ.submatrix e id * U₀.submatrix id e = 1
    rw [← submatrix_mul _ _ e id e Function.bijective_id, hU₀, submatrix_one_equiv]
  · change U₀.submatrix id e * U₀ᵀ.submatrix e id = 1
    rw [submatrix_mul_equiv _ _ id e id, hU₀']
    rfl
  · change U₀ᵀ.submatrix e id * A.submatrix id id * U₀.submatrix id e = _
    rw [← submatrix_mul _ _ e id id Function.bijective_id,
      ← submatrix_mul _ _ e id e Function.bijective_id, hD₀, submatrix_diagonal_equiv]
    apply congrArg diagonal
    funext j
    simp [e, Matrix.IsHermitian.eigenvalues, descendingEigenvalue]

end MF21Challenge

namespace MF21Audit

theorem mulVec_norm_sq {n N : ℕ} (W : Matrix (Fin N) (Fin n) ℝ)
    (hW : Wᵀ * W = 1) (x : Fin n → ℝ) :
    ∑ i, (W *ᵥ x) i ^ 2 = ∑ j, (x j)^2 := by
  calc
    _ = (W *ᵥ x) ⬝ᵥ (W *ᵥ x) := by simp only [dotProduct, pow_two]
    _ = x ⬝ᵥ ((Wᵀ * W) *ᵥ x) := by
      symm
      rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    _ = _ := by rw [hW, one_mulVec]; simp only [dotProduct, pow_two]

theorem mulVec_diagonal_quad {n N : ℕ} (W : Matrix (Fin N) (Fin n) ℝ)
    (lam : Fin N → ℝ) (μ : Fin n → ℝ)
    (hW : Wᵀ * diagonal lam * W = diagonal μ) (x : Fin n → ℝ) :
    ∑ i, lam i * (W *ᵥ x) i ^ 2 = ∑ j, μ j * (x j)^2 := by
  calc
    _ = (W *ᵥ x) ⬝ᵥ (diagonal lam *ᵥ (W *ᵥ x)) := by
      simp only [dotProduct, mulVec_diagonal, pow_two]
      apply sum_congr rfl
      intro i _
      ring
    _ = x ⬝ᵥ ((Wᵀ * diagonal lam * W) *ᵥ x) := by
      symm
      rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    _ = _ := by
      rw [hW]
      simp only [dotProduct, mulVec_diagonal, pow_two]
      apply sum_congr rfl
      intro j _
      ring

end MF21Audit

namespace MF21Challenge

theorem exists_compression_coordinates {n N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (E : Matrix (Fin N) (Fin n) ℝ) (hE : Eᵀ * E = 1) (hcomp : Eᵀ * A * E = B) :
    ∃ W : (Fin n → ℝ) →ₗ[ℝ] (Fin N → ℝ),
      (∀ x, ∑ i, (W x i)^2 = ∑ j, (x j)^2) ∧
      (∀ x, ∑ i, descendingEigenvalue hA i * (W x i)^2 =
        ∑ j, descendingEigenvalue hB j * (x j)^2) := by
  obtain ⟨U, hU, hU', hDU⟩ := exists_ordered_diagonalization hA
  obtain ⟨V, hV, hV', hDV⟩ := exists_ordered_diagonalization hB
  let W := Uᵀ * E * V
  have hW : Wᵀ * W = 1 := by
    calc
      _ = Vᵀ * Eᵀ * (U * Uᵀ) * E * V := by
        simp only [W, transpose_mul, transpose_transpose]
        simp only [Matrix.mul_assoc]
      _ = Vᵀ * (Eᵀ * E) * V := by rw [hU']; simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = 1 := by rw [hE, Matrix.mul_one, hV]
  have hDW : Wᵀ * diagonal (descendingEigenvalue hA) * W =
      diagonal (descendingEigenvalue hB) := by
    rw [← hDU]
    calc
      _ = Vᵀ * Eᵀ * (U * Uᵀ) * A * (U * Uᵀ) * E * V := by
        simp only [W, transpose_mul, transpose_transpose]
        simp only [Matrix.mul_assoc]
      _ = Vᵀ * (Eᵀ * A * E) * V := by rw [hU']; simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = _ := by rw [hcomp, hDV]
  exact ⟨W.mulVecLin, MF21Audit.mulVec_norm_sq W hW,
    MF21Audit.mulVec_diagonal_quad W _ _ hDW⟩

theorem compression_interlacing {n N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (E : Matrix (Fin N) (Fin n) ℝ) (hE : Eᵀ * E = 1)
    (hcomp : Eᵀ * A * E = B) (hnN : n ≤ N) (k : ℕ) (hkn : k < n) :
    descendingEigenvalue hA ⟨N - n + k, by omega⟩ ≤ descendingEigenvalue hB ⟨k, hkn⟩ ∧
    descendingEigenvalue hB ⟨k, hkn⟩ ≤ descendingEigenvalue hA ⟨k, hkn.trans_le hnN⟩ := by
  obtain ⟨W, hnorm, hquad⟩ := exists_compression_coordinates A B hA hB E hE hcomp
  exact ⟨MF21Audit.diagonal_compression_antitone_ge _ _ W
    (descendingEigenvalue_antitone hA) (descendingEigenvalue_antitone hB) hnN hnorm hquad k hkn,
    MF21Audit.diagonal_compression_antitone_le _ _ W
    (descendingEigenvalue_antitone hA) (descendingEigenvalue_antitone hB)
    hnorm hquad k hkn (hkn.trans_le hnN)⟩

def coordinateEmbedding {n N : ℕ} (f : Fin n → Fin N) : Matrix (Fin N) (Fin n) ℝ :=
  fun i j ↦ if i = f j then 1 else 0

theorem coordinateEmbedding_isometry {n N : ℕ} (f : Fin n → Fin N)
    (hf : Function.Injective f) : (coordinateEmbedding f)ᵀ * coordinateEmbedding f = 1 := by
  ext i j
  simp [Matrix.mul_apply, coordinateEmbedding, Matrix.transpose_apply,
    Matrix.one_apply, hf.eq_iff, eq_comm]

theorem coordinateEmbedding_compression {n N : ℕ} (f : Fin n → Fin N)
    (A : Matrix (Fin N) (Fin N) ℝ) :
    (coordinateEmbedding f)ᵀ * A * coordinateEmbedding f = A.submatrix f f := by
  ext i j
  simp [Matrix.mul_apply, coordinateEmbedding, Matrix.transpose_apply,
    Matrix.submatrix_apply]

/-- Cauchy interlacing for any injectively selected principal submatrix,
with the actual sorted Hermitian eigenvalues and the exact codimension. -/
theorem principal_submatrix_interlacing {n N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian)
    (f : Fin n → Fin N) (hf : Function.Injective f)
    (k : ℕ) (hkn : k < n) :
    let hB := hA.submatrix f
    descendingEigenvalue hA ⟨N - n + k, by
      have hnN : n ≤ N := by simpa using Fintype.card_le_of_injective f hf
      omega⟩ ≤
        descendingEigenvalue hB ⟨k, hkn⟩ ∧
    descendingEigenvalue hB ⟨k, hkn⟩ ≤
        descendingEigenvalue hA ⟨k, by
          have hnN : n ≤ N := by simpa using Fintype.card_le_of_injective f hf
          omega⟩ := by
  have hnN : n ≤ N := by simpa using Fintype.card_le_of_injective f hf
  exact compression_interlacing A (A.submatrix f f) hA (hA.submatrix f)
    (coordinateEmbedding f) (coordinateEmbedding_isometry f hf)
    (coordinateEmbedding_compression f A) hnN k hkn

end MF21Challenge

#print axioms MF21Audit.diagonal_compression_antitone_le
#print axioms MF21Audit.diagonal_compression_antitone_ge
#print axioms MF21Challenge.exists_ordered_diagonalization
#print axioms MF21Challenge.compression_interlacing
#print axioms MF21Challenge.principal_submatrix_interlacing
