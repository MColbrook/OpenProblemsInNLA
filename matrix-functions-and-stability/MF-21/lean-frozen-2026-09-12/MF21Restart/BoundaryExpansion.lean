import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
The concrete boundary determinant (13) and its column-multilinear grouped
expansion. Root moduli are unrestricted; in particular this permits the
exterior roots that the previous raw-root estimates excluded.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

def boundaryMatrix (m n : ℕ) (w : Fin (2 * m) → ℂ) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ :=
  Matrix.of fun row col => if row.val < m then w col ^ row.val else w col ^ (n + row.val)

def boundaryUpper (m : ℕ) (w : Fin (2 * m) → ℂ) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ :=
  Matrix.of fun row col => if row.val < m then w col ^ row.val else 0

def boundaryLower (m : ℕ) (w : Fin (2 * m) → ℂ) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ :=
  Matrix.of fun row col => if row.val < m then 0 else w col ^ (row.val - m)

def boundaryCoefficient (m : ℕ) (w : Fin (2 * m) → ℂ)
    (s : Finset (Fin (2 * m))) : ℂ :=
  Matrix.det (Matrix.of fun row col => if col ∈ s then boundaryLower m w row col
    else boundaryUpper m w row col)

lemma boundaryMatrix_split (m n : ℕ) (w : Fin (2 * m) → ℂ) :
    boundaryMatrix m n w = Matrix.of fun row col =>
      boundaryUpper m w row col + w col ^ (n + m) * boundaryLower m w row col := by
  funext row col
  by_cases hr : row.val < m
  · simp [boundaryMatrix, boundaryUpper, boundaryLower, hr]
  · simp only [boundaryMatrix, boundaryUpper, boundaryLower, Matrix.of_apply, if_neg hr, zero_add]
    rw [← pow_add]
    congr 1
    omega

set_option backward.isDefEq.respectTransparency.types false in
/-- Multilinearity grouped by the columns selected from the second matrix.
Using the transpose explicitly fixes the determinant's column convention. -/
lemma det_column_split {ι K : Type*} [Fintype ι] [DecidableEq ι] [CommRing K]
    (U L : Matrix ι ι K) (c : ι → K) :
    Matrix.det (Matrix.of fun i j => U i j + c j * L i j) =
      ∑ s : Finset ι, (∏ j ∈ s, c j) *
        Matrix.det (Matrix.of fun i j => if j ∈ s then L i j else U i j) := by
  classical
  let D := (Matrix.detRowAlternating : (ι → K) [⋀^ι]→ₗ[K] K)
  rw [← Matrix.det_transpose (Matrix.of (fun i j => U i j + c j * L i j))]
  have hrows : (Matrix.of (fun i j => U i j + c j * L i j)).transpose =
      Matrix.of ((fun j => c j • L.transpose j) + (fun j => U.transpose j)) := by
    funext j i
    simp [Matrix.transpose_apply, add_comm]
  rw [hrows]
  change D ((fun j => c j • L.transpose j) + (fun j => U.transpose j)) = _
  rw [D.map_add_univ]
  apply Finset.sum_congr rfl
  intro s _
  have hsplit : s.piecewise (fun j => c j • L.transpose j) (fun j => U.transpose j) =
      fun j => (if j ∈ s then c j else 1) •
        s.piecewise (fun j => L.transpose j) (fun j => U.transpose j) j := by
    funext j i
    by_cases hj : j ∈ s <;> simp [Finset.piecewise, hj]
  rw [hsplit, D.map_smul_univ]
  simp only [Finset.prod_ite_mem, Finset.univ_inter, smul_eq_mul]
  congr 1
  change Matrix.det (Matrix.of (s.piecewise (fun j => L.transpose j)
    (fun j => U.transpose j))) = _
  rw [← Matrix.det_transpose]
  congr 1
  ext i j
  by_cases hj : j ∈ s <;> simp [Finset.piecewise, Matrix.transpose_apply, hj]

theorem boundaryDeterminant_grouped_expansion
    (m n : ℕ) (w : Fin (2 * m) → ℂ) :
    (boundaryMatrix m n w).det =
      ∑ s : Finset (Fin (2 * m)), boundaryCoefficient m w s *
        (∏ j ∈ s, w j) ^ (n + m) := by
  rw [boundaryMatrix_split, det_column_split]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.prod_pow]
  exact mul_comm _ _

def boundaryBottomRows (m : ℕ) : Finset (Fin (2 * m)) :=
  Finset.univ.filter fun i => m ≤ i.val

lemma card_boundaryBottomRows (m : ℕ) : (boundaryBottomRows m).card = m := by
  let f : Fin m → Fin (2 * m) := fun i => ⟨m + i.val, by omega⟩
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    dsimp [f] at hv
    omega
  have heq : boundaryBottomRows m = Finset.univ.image f := by
    ext i
    simp only [boundaryBottomRows, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · intro hi
      refine ⟨⟨i.val - m, by omega⟩, ?_⟩
      apply Fin.ext
      dsimp [f]
      omega
    · rintro ⟨j, rfl⟩
      dsimp [f]
      omega
  rw [heq, Finset.card_image_of_injective _ hinj]
  exact Finset.card_fin m

/-- A surviving permutation maps the selected *columns* exactly onto the
lower rows. This establishes the subset cardinality without assuming roots
are nonzero or trying to bound individual exterior-root monomials. -/
theorem boundaryCoefficient_eq_zero_of_card_ne
    (m : ℕ) (w : Fin (2 * m) → ℂ) (s : Finset (Fin (2 * m)))
    (hcard : s.card ≠ m) : boundaryCoefficient m w s = 0 := by
  classical
  by_contra hdet
  rw [boundaryCoefficient, Matrix.det_apply'] at hdet
  obtain ⟨σ, _, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdet
  have hp := (mul_ne_zero_iff.mp hterm).2
  have hmem : ∀ col, col ∈ s ↔ m ≤ (σ col).val := by
    intro col
    have he := Finset.prod_ne_zero_iff.mp hp col (Finset.mem_univ _)
    constructor
    · intro hc
      by_contra hlt
      have hl : (σ col).val < m := by omega
      exact he (by simp [hc, boundaryLower, hl])
    · intro hr
      by_contra hc
      have hl : ¬(σ col).val < m := by omega
      exact he (by simp [hc, boundaryUpper, hl])
  have himage : s.image σ = boundaryBottomRows m := by
    ext row
    simp only [Finset.mem_image, boundaryBottomRows, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨col, hc, rfl⟩
      exact (hmem col).mp hc
    · intro hr
      refine ⟨σ.symm row, ?_, σ.apply_symm_apply row⟩
      exact (hmem _).mpr (by simpa using hr)
  apply hcard
  rw [← Finset.card_image_of_injective s σ.injective, himage, card_boundaryBottomRows]

theorem boundaryDeterminant_card_grouped_expansion
    (m n : ℕ) (w : Fin (2 * m) → ℂ) :
    (boundaryMatrix m n w).det =
      ∑ s ∈ (Finset.univ : Finset (Fin (2 * m))).powersetCard m,
        boundaryCoefficient m w s * (∏ j ∈ s, w j) ^ (n + m) := by
  classical
  rw [boundaryDeterminant_grouped_expansion]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro s _ hs
  have hcard : s.card ≠ m := by
    simpa only [Finset.mem_powersetCard, Finset.subset_univ, true_and] using hs
  rw [boundaryCoefficient_eq_zero_of_card_ne m w s hcard, zero_mul]

lemma boundary_compl_card {m : ℕ} {s : Finset (Fin (2 * m))}
    (hs : s.card = m) : sᶜ.card = m := by
  rw [Finset.card_compl, Fintype.card_fin, hs]
  omega

/-- The column order used in the Laplace expansion: the inherited-order
complement first, then the inherited-order selected subset. -/
def boundaryColumnEquiv (m : ℕ) (s : Finset (Fin (2 * m))) (hs : s.card = m) :
    (Fin m ⊕ Fin m) ≃ Fin (2 * m) := by
  let a := sᶜ.orderEmbOfFin (boundary_compl_card hs)
  let b := s.orderEmbOfFin hs
  refine Equiv.ofBijective (Sum.elim a b) ⟨?_, ?_⟩
  · intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (a.injective hij)
      | inr j =>
        change a i = b j at hij
        have hnot : a i ∉ s := Finset.mem_compl.mp (sᶜ.orderEmbOfFin_mem _ i)
        have hyes : b j ∈ s := s.orderEmbOfFin_mem _ j
        exact False.elim (hnot (hij.symm ▸ hyes))
    | inr i =>
      cases j with
      | inl j =>
        change b i = a j at hij
        have hnot : a j ∉ s := Finset.mem_compl.mp (sᶜ.orderEmbOfFin_mem _ j)
        have hyes : b i ∈ s := s.orderEmbOfFin_mem _ i
        exact False.elim (hnot (hij ▸ hyes))
      | inr j => exact congrArg Sum.inr (b.injective hij)
  · intro x
    by_cases hx : x ∈ s
    · refine ⟨Sum.inr ((s.orderIsoOfFin hs).symm ⟨x, hx⟩), ?_⟩
      exact congrArg Subtype.val ((s.orderIsoOfFin hs).apply_symm_apply ⟨x, hx⟩)
    · refine ⟨Sum.inl ((sᶜ.orderIsoOfFin (boundary_compl_card hs)).symm
        ⟨x, Finset.mem_compl.mpr hx⟩), ?_⟩
      exact congrArg Subtype.val
        ((sᶜ.orderIsoOfFin (boundary_compl_card hs)).apply_symm_apply
          ⟨x, Finset.mem_compl.mpr hx⟩)

lemma boundaryColumnEquiv_inl (m : ℕ) (s : Finset (Fin (2 * m)))
    (hs : s.card = m) (i : Fin m) :
    boundaryColumnEquiv m s hs (Sum.inl i) =
      sᶜ.orderEmbOfFin (boundary_compl_card hs) i := rfl

lemma boundaryColumnEquiv_inr (m : ℕ) (s : Finset (Fin (2 * m)))
    (hs : s.card = m) (i : Fin m) :
    boundaryColumnEquiv m s hs (Sum.inr i) = s.orderEmbOfFin hs i := rfl

def boundaryRowEquiv (m : ℕ) : (Fin m ⊕ Fin m) ≃ Fin (2 * m) :=
  finSumFinEquiv.trans (finCongr (by omega))

lemma boundaryRowEquiv_inl_val (m : ℕ) (i : Fin m) :
    (boundaryRowEquiv m (Sum.inl i)).val = i.val := rfl

lemma boundaryRowEquiv_inr_val (m : ℕ) (i : Fin m) :
    (boundaryRowEquiv m (Sum.inr i)).val = m + i.val := rfl

/-- Reordering the split columns displays the two actual Vandermonde blocks.
The transpose reflects the manuscript convention: powers are row indices. -/
theorem boundaryCoefficient_block_matrix
    (m : ℕ) (w : Fin (2 * m) → ℂ) (s : Finset (Fin (2 * m))) (hs : s.card = m) :
    (Matrix.of fun row col => if col ∈ s then boundaryLower m w row col
      else boundaryUpper m w row col).submatrix
        (boundaryRowEquiv m) (boundaryColumnEquiv m s hs) =
      Matrix.fromBlocks
        (Matrix.vandermonde (fun i => w (sᶜ.orderEmbOfFin (boundary_compl_card hs) i))).transpose
        0 0 (Matrix.vandermonde (fun i => w (s.orderEmbOfFin hs i))).transpose := by
  ext (i | i) (j | j)
  · have hj : sᶜ.orderEmbOfFin (boundary_compl_card hs) j ∉ s :=
      Finset.mem_compl.mp (sᶜ.orderEmbOfFin_mem _ j)
    simp [Matrix.submatrix_apply, boundaryColumnEquiv_inl, boundaryUpper, hj,
      boundaryRowEquiv_inl_val, i.isLt, Matrix.transpose_apply]
  · have hj := s.orderEmbOfFin_mem hs j
    simp [Matrix.submatrix_apply, boundaryColumnEquiv_inr, boundaryLower, hj,
      boundaryRowEquiv_inl_val, i.isLt]
  · have hj : sᶜ.orderEmbOfFin (boundary_compl_card hs) j ∉ s :=
      Finset.mem_compl.mp (sᶜ.orderEmbOfFin_mem _ j)
    simp [Matrix.submatrix_apply, boundaryColumnEquiv_inl, boundaryUpper, hj,
      boundaryRowEquiv_inr_val]
  · have hj := s.orderEmbOfFin_mem hs j
    simp [Matrix.submatrix_apply, boundaryColumnEquiv_inr, boundaryLower, hj,
      boundaryRowEquiv_inr_val, Matrix.transpose_apply]

def boundaryLaplaceSign (m : ℕ) (s : Finset (Fin (2 * m))) (hs : s.card = m) : ℤˣ :=
  Equiv.Perm.sign ((boundaryColumnEquiv m s hs).symm.trans (boundaryRowEquiv m))

/-- The surviving coefficient is the signed product of the two
inherited-order Vandermonde determinants, exactly as in equation (14). -/
theorem boundaryCoefficient_vandermonde
    (m : ℕ) (w : Fin (2 * m) → ℂ) (s : Finset (Fin (2 * m))) (hs : s.card = m) :
    boundaryCoefficient m w s =
      (↑↑(boundaryLaplaceSign m s hs) : ℂ) *
        (Matrix.vandermonde (fun i => w (sᶜ.orderEmbOfFin (boundary_compl_card hs) i))).det *
        (Matrix.vandermonde (fun i => w (s.orderEmbOfFin hs i))).det := by
  let M := Matrix.of fun row col => if col ∈ s then boundaryLower m w row col
    else boundaryUpper m w row col
  have hr := Matrix.det_reindex (boundaryRowEquiv m).symm
    (boundaryColumnEquiv m s hs).symm M
  have heq :
      (Matrix.vandermonde (fun i => w (sᶜ.orderEmbOfFin (boundary_compl_card hs) i))).det *
        (Matrix.vandermonde (fun i => w (s.orderEmbOfFin hs i))).det =
      (↑↑(boundaryLaplaceSign m s hs) : ℂ) * boundaryCoefficient m w s := by
    simpa only [M, Matrix.reindex_apply, Equiv.symm_symm,
      boundaryCoefficient_block_matrix, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_transpose, boundaryLaplaceSign, boundaryCoefficient] using hr
  rcases Int.units_eq_one_or (boundaryLaplaceSign m s hs) with hsign | hsign
  · simpa [hsign] using heq.symm
  · have hneg := congrArg Neg.neg heq
    simp [hsign] at hneg ⊢
    simpa only [neg_mul] using hneg.symm

#print axioms boundaryDeterminant_grouped_expansion
#print axioms boundaryCoefficient_eq_zero_of_card_ne
#print axioms boundaryDeterminant_card_grouped_expansion
#print axioms boundaryCoefficient_vandermonde

end MF21Restart
