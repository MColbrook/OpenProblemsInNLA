import MF21.RecurrenceBasis
import MF21.FirstInverseColumn

/-! Exact boundary-determinant reduction for the actual Toeplitz matrix.
The root conditions are explicit hypotheses; spectral equivalence is proved. -/
noncomputable section
open scoped BigOperators
open Finset Matrix Polynomial
set_option backward.isDefEq.respectTransparency.types false
namespace MF21Boundary

abbrev central (m l : ℕ) : ℂ := (MF21FirstColumn.central m l : ℝ)

def recurrence (m : ℕ) (lam : ℂ) : LinearRecurrence ℂ where
  order := 2 * m
  coeffs i := ((if i.val = m then lam else 0) - central m i.val) / central m (2 * m)

def padded (m n : ℕ) (u : ℕ → ℂ) (k : ℕ) : ℂ :=
  if m ≤ k ∧ k < m + n then u (k - m) else 0

def extend (n : ℕ) (v : Fin n → ℂ) (j : ℕ) : ℂ :=
  if h : j < n then v ⟨j, h⟩ else 0

def toeplitz (m n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j ↦ (MF21Challenge.toeplitz m n i j : ℂ)

def ghostIndex (m n : ℕ) (i : Fin (2 * m)) : ℕ :=
  if i.val < m then i.val else n + i.val

def boundaryMatrix (m n : ℕ) (roots : Fin (2 * m) → ℂ) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ :=
  fun i j ↦ (roots j) ^ ghostIndex m n i

/-- Any finite recurrence segment extends to the unique global recurrence solution. -/
theorem finite_extension (E : LinearRecurrence ℂ) (n : ℕ) (u : ℕ → ℂ)
    (hu : ∀ k < n, u (k + E.order) = ∑ i, E.coeffs i * u (k + i)) :
    ∀ k < n + E.order, E.mkSol (fun i ↦ u i) k = u k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    by_cases hsmall : k < E.order
    · exact E.mkSol_eq_init _ ⟨k, hsmall⟩
    · have hbig : E.order ≤ k := Nat.le_of_not_gt hsmall
      have hkn : k - E.order < n := by omega
      have he : k - E.order + E.order = k := by omega
      rw [← he, E.is_sol_mkSol, hu (k - E.order) hkn]
      apply sum_congr rfl
      intro i hi
      rw [ih (k - E.order + i.val) (by omega) (by omega)]

theorem central_last (m : ℕ) : central m (2 * m) = (-1 : ℂ) ^ m := by
  simp only [central, MF21FirstColumn.central, Nat.choose_self, Nat.cast_one, mul_one,
    Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one]
  rw [show m + 2 * m = m + 2 * m by rfl, pow_add, pow_mul]
  norm_num

theorem central_last_ne_zero (m : ℕ) : central m (2 * m) ≠ 0 := by
  rw [central_last]
  exact pow_ne_zero _ (by norm_num)

/-- The normalized forward recurrence is exactly the centered Toeplitz equation. -/
theorem recurrence_at_iff (m : ℕ) (hm : 0 < m) (lam : ℂ) (u : ℕ → ℂ) (k : ℕ) :
    u (k + 2 * m) = ∑ i : Fin (2 * m), (recurrence m lam).coeffs i * u (k + i) ↔
      (∑ l ∈ range (2 * m + 1), central m l * u (k + l)) = lam * u (k + m) := by
  have hmfin : m < 2 * m := by omega
  have hsingle : (∑ i : Fin (2 * m),
      (if i.val = m then lam else 0) * u (k + i.val)) = lam * u (k + m) := by
    rw [sum_eq_single (⟨m, hmfin⟩ : Fin (2 * m))]
    · simp
    · intro i hi hne
      have hv : i.val ≠ m := fun hv ↦ hne (Fin.ext hv)
      simp [hv]
    · simp
  have hsum : (∑ i : Fin (2 * m), (recurrence m lam).coeffs i * u (k + i.val)) =
      (lam * u (k + m) - ∑ l ∈ range (2 * m), central m l * u (k + l)) /
        central m (2 * m) := by
    simp only [recurrence, div_mul_eq_mul_div, sub_mul, ← sum_div, sum_sub_distrib, hsingle]
    rw [Fin.sum_univ_eq_sum_range (fun l ↦ central m l * u (k + l)) (2 * m)]
  rw [hsum, eq_div_iff (central_last_ne_zero m), sum_range_succ]
  constructor <;> intro h <;> linear_combination h

theorem padded_re (m n : ℕ) (u : ℕ → ℂ) (k : ℕ) :
    (padded m n u k).re = MF21FirstColumn.padded m n (fun j ↦ (u j).re) k := by
  by_cases h : m ≤ k ∧ k < m + n <;> simp [padded, MF21FirstColumn.padded, h]

theorem padded_im (m n : ℕ) (u : ℕ → ℂ) (k : ℕ) :
    (padded m n u k).im = MF21FirstColumn.padded m n (fun j ↦ (u j).im) k := by
  by_cases h : m ≤ k ∧ k < m + n <;> simp [padded, MF21FirstColumn.padded, h]

theorem row_convolution (m n i : ℕ) (u : ℕ → ℂ) :
    (∑ j ∈ range n, (MF21Challenge.coefficient m (Nat.dist i j) : ℂ) * u j) =
      ∑ l ∈ range (2 * m + 1), central m l * padded m n u (i + l) := by
  apply Complex.ext
  · simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, padded_re] using
      MF21FirstColumn.row_convolution m n i (fun j ↦ (u j).re)
  · simpa only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, padded_im] using
      MF21FirstColumn.row_convolution m n i (fun j ↦ (u j).im)

theorem extend_apply (n : ℕ) (v : Fin n → ℂ) (j : Fin n) : extend n v j.val = v j := by
  simp [extend, j.isLt]

theorem matrix_row_convolution (m n : ℕ) (v : Fin n → ℂ) (i : Fin n) :
    (toeplitz m n).mulVec v i =
      ∑ l ∈ range (2 * m + 1), central m l * padded m n (extend n v) (i.val + l) := by
  rw [← row_convolution]
  change (∑ j : Fin n, (MF21Challenge.coefficient m (Nat.dist i.val j.val) : ℂ) * v j) = _
  have h := Fin.sum_univ_eq_sum_range
    (fun j ↦ (MF21Challenge.coefficient m (Nat.dist i.val j) : ℂ) * extend n v j) n
  simpa only [extend_apply] using h

theorem padded_interior (m n : ℕ) (v : Fin n → ℂ) (i : Fin n) :
    padded m n (extend n v) (i.val + m) = v i := by
  have hi := i.isLt
  simp [padded, show m ≤ i.val + m by omega, show i.val + m < m + n by omega,
    extend_apply]

theorem eigenvector_iff_finite_recurrence (m n : ℕ) (hm : 0 < m) (lam : ℂ)
    (v : Fin n → ℂ) :
    (toeplitz m n).mulVec v = lam • v ↔
      ∀ k < n, padded m n (extend n v) (k + 2 * m) =
        ∑ i : Fin (2 * m), (recurrence m lam).coeffs i *
          padded m n (extend n v) (k + i.val) := by
  constructor
  · intro h k hk
    apply (recurrence_at_iff m hm lam _ k).mpr
    have he := congrFun h (⟨k, hk⟩ : Fin n)
    rw [matrix_row_convolution] at he
    rw [padded_interior m n v (⟨k, hk⟩ : Fin n)]
    exact he
  · intro h
    funext i
    have he := (recurrence_at_iff m hm lam _ i.val).mp (h i.val i.isLt)
    rw [← matrix_row_convolution, padded_interior] at he
    exact he

def Ghosts (m n : ℕ) (u : ℕ → ℂ) : Prop :=
  (∀ k < m, u k = 0) ∧ (∀ k, n + m ≤ k → k < n + 2 * m → u k = 0)

theorem padded_ghosts (m n : ℕ) (u : ℕ → ℂ) : Ghosts m n (padded m n u) := by
  constructor
  · intro k hk
    simp [padded, show ¬m ≤ k by omega]
  · intro k hlo hhi
    simp [padded, show ¬k < m + n by omega]

theorem ghosts_of_agreement (m n : ℕ) (u w : ℕ → ℂ)
    (hw : Ghosts m n w) (he : ∀ k < n + 2 * m, u k = w k) : Ghosts m n u := by
  constructor
  · intro k hk
    rw [he k (by omega), hw.1 k hk]
  · intro k hlo hhi
    rw [he k hhi, hw.2 k hlo hhi]

def interior (m n : ℕ) (u : ℕ → ℂ) : Fin n → ℂ := fun i ↦ u (i.val + m)

theorem padded_interior_agrees (m n : ℕ) (u : ℕ → ℂ) (hg : Ghosts m n u)
    (k : ℕ) (hk : k < n + 2 * m) :
    padded m n (extend n (interior m n u)) k = u k := by
  by_cases hlo : m ≤ k
  · by_cases hhi : k < m + n
    · have hidx : k - m < n := by omega
      simp [padded, hlo, hhi, extend, hidx, interior, Nat.sub_add_cancel hlo]
    · rw [hg.2 k (by omega) hk]
      simp [padded, hhi]
  · rw [hg.1 k (by omega)]
    simp [padded, hlo]

theorem solution_ghosts_gives_eigenvector (m n : ℕ) (hm : 0 < m) (lam : ℂ)
    (u : ℕ → ℂ) (hu : (recurrence m lam).IsSolution u) (hg : Ghosts m n u) :
    (toeplitz m n).mulVec (interior m n u) = lam • interior m n u := by
  apply (eigenvector_iff_finite_recurrence m n hm lam _).mpr
  intro k hk
  rw [padded_interior_agrees m n u hg _ (by omega)]
  change u (k + (recurrence m lam).order) = _
  rw [hu k]
  apply sum_congr rfl
  intro i hi
  rw [padded_interior_agrees m n u hg _ (by have hi' : i.val < 2 * m := i.isLt; omega)]

def geometric (m : ℕ) (roots c : Fin (2 * m) → ℂ) (k : ℕ) : ℂ :=
  ∑ j, c j * (roots j) ^ k

theorem boundary_mulVec (m n : ℕ) (roots c : Fin (2 * m) → ℂ) (i : Fin (2 * m)) :
    (boundaryMatrix m n roots).mulVec c i = geometric m roots c (ghostIndex m n i) := by
  simp only [boundaryMatrix, Matrix.mulVec, dotProduct, geometric]
  apply sum_congr rfl
  intro j hj
  ring

theorem boundary_kernel_iff_ghosts (m n : ℕ) (roots c : Fin (2 * m) → ℂ) :
    (boundaryMatrix m n roots).mulVec c = 0 ↔ Ghosts m n (geometric m roots c) := by
  constructor
  · intro h
    constructor
    · intro k hk
      have hkfin : k < 2 * m := by omega
      have he := congrFun h (⟨k, hkfin⟩ : Fin (2 * m))
      simpa only [boundary_mulVec, ghostIndex, hk, if_pos, Pi.zero_apply] using he
    · intro k hlo hhi
      have hkfin : k - n < 2 * m := by omega
      have he := congrFun h (⟨k - n, hkfin⟩ : Fin (2 * m))
      have hklo : ¬k - n < m := by omega
      have heq : n + (k - n) = k := by omega
      simpa [boundary_mulVec, ghostIndex, hklo, heq] using he
  · intro h
    funext i
    rw [boundary_mulVec]
    simp only [ghostIndex, Pi.zero_apply]
    split_ifs with hi
    · exact h.1 i.val hi
    · exact h.2 (n + i.val) (by omega) (by have := i.isLt; omega)

theorem eigenvector_has_geometric_representation (m n : ℕ) (hm : 0 < m) (lam : ℂ)
    (roots : Fin (2 * m) → ℂ) (hinj : Function.Injective roots)
    (hr : ∀ j, (recurrence m lam).charPoly.IsRoot (roots j))
    (v : Fin n → ℂ) (hv : (toeplitz m n).mulVec v = lam • v) :
    ∃ c : Fin (2 * m) → ℂ,
      (boundaryMatrix m n roots).mulVec c = 0 ∧ interior m n (geometric m roots c) = v := by
  let E := recurrence m lam
  let w := padded m n (extend n v)
  let u := E.mkSol (fun i ↦ w i.val)
  have hu : E.IsSolution u := E.is_sol_mkSol _
  have he : ∀ k < n + 2 * m, u k = w k :=
    finite_extension E n w ((eigenvector_iff_finite_recurrence m n hm lam v).mp hv)
  obtain ⟨c, hc⟩ := MF21Recurrence.solution_eq_geometric_combination E roots hinj hr u hu
  change ∀ k, u k = geometric m roots c k at hc
  refine ⟨c, ?_, ?_⟩
  · apply (boundary_kernel_iff_ghosts m n roots c).mpr
    apply ghosts_of_agreement m n _ w (padded_ghosts m n _)
    intro k hk
    exact (hc k).symm.trans (he k hk)
  · funext i
    change geometric m roots c (i.val + m) = v i
    rw [← hc, he _ (by have := i.isLt; omega)]
    exact padded_interior m n v i

/-- Restriction to the interior is injective on the boundary kernel. -/
theorem boundary_kernel_restriction_injective (m n : ℕ)
    (roots : Fin (2 * m) → ℂ) (hinj : Function.Injective roots)
    (c : Fin (2 * m) → ℂ) (hc : (boundaryMatrix m n roots).mulVec c = 0)
    (hz : interior m n (geometric m roots c) = 0) : c = 0 := by
  have hg := (boundary_kernel_iff_ghosts m n roots c).mp hc
  apply MF21Recurrence.geometric_coefficients_unique roots c 0 hinj
  intro k
  have he := padded_interior_agrees m n (geometric m roots c) hg k.val
    (by have := k.isLt; omega)
  rw [hz] at he
  have hezero : padded m n (extend n (0 : Fin n → ℂ)) k.val = 0 := by
    simp [padded, extend]
  rw [hezero] at he
  simpa only [geometric, Pi.zero_apply, zero_mul, sum_const_zero] using he.symm

/-- Exact equivalence of nonzero eigenvectors and nonzero boundary coefficients. -/
theorem eigenvector_iff_boundary_kernel (m n : ℕ) (hm : 0 < m) (lam : ℂ)
    (roots : Fin (2 * m) → ℂ) (hinj : Function.Injective roots)
    (hr : ∀ j, (recurrence m lam).charPoly.IsRoot (roots j)) :
    (∃ v : Fin n → ℂ, v ≠ 0 ∧ (toeplitz m n).mulVec v = lam • v) ↔
      ∃ c : Fin (2 * m) → ℂ, c ≠ 0 ∧ (boundaryMatrix m n roots).mulVec c = 0 := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    obtain ⟨c, hc, he⟩ := eigenvector_has_geometric_representation m n hm lam roots hinj hr v hv
    refine ⟨c, ?_, hc⟩
    intro hc0
    apply hv0
    rw [← he, hc0]
    ext i
    simp [interior, geometric]
  · rintro ⟨c, hc0, hc⟩
    refine ⟨interior m n (geometric m roots c), ?_, ?_⟩
    · exact fun hz ↦ hc0 (boundary_kernel_restriction_injective m n roots hinj c hc hz)
    · apply solution_ghosts_gives_eigenvector m n hm lam
      · exact MF21Recurrence.geometric_combination_solution (recurrence m lam) roots c hr
      · exact (boundary_kernel_iff_ghosts m n roots c).mp hc

/-- The ghost determinant detects eigenvalues of the actual complexified Toeplitz matrix. -/
theorem eigenvector_iff_boundary_det_zero (m n : ℕ) (hm : 0 < m) (lam : ℂ)
    (roots : Fin (2 * m) → ℂ) (hinj : Function.Injective roots)
    (hr : ∀ j, (recurrence m lam).charPoly.IsRoot (roots j)) :
    (∃ v : Fin n → ℂ, v ≠ 0 ∧ (toeplitz m n).mulVec v = lam • v) ↔
      (boundaryMatrix m n roots).det = 0 := by
  rw [eigenvector_iff_boundary_kernel m n hm lam roots hinj hr]
  exact Matrix.exists_mulVec_eq_zero_iff

/-- The boundary coefficients restrict linearly to actual matrix eigenvectors. -/
def boundaryToEigenspace (m n : ℕ) (hm : 0 < m) (lam : ℂ)
    (roots : Fin (2 * m) → ℂ)
    (hr : ∀ j, (recurrence m lam).charPoly.IsRoot (roots j)) :
    LinearMap.ker (boundaryMatrix m n roots).mulVecLin →ₗ[ℂ]
      Module.End.eigenspace (toeplitz m n).mulVecLin lam where
  toFun c := ⟨interior m n (geometric m roots c.val), by
    apply Module.End.mem_eigenspace_iff.mpr
    exact solution_ghosts_gives_eigenvector m n hm lam _
      (MF21Recurrence.geometric_combination_solution (recurrence m lam) roots c.val hr)
      ((boundary_kernel_iff_ghosts m n roots c.val).mp c.property)⟩
  map_add' c d := by
    apply Subtype.ext
    funext i
    simp [interior, geometric, add_mul, sum_add_distrib]
  map_smul' a c := by
    apply Subtype.ext
    funext i
    simp [interior, geometric, mul_assoc, mul_sum]

/-- The ghost system has exactly the dimension of the true eigenspace. -/
def boundaryKernelEquivEigenspace (m n : ℕ) (hm : 0 < m) (lam : ℂ)
    (roots : Fin (2 * m) → ℂ) (hinj : Function.Injective roots)
    (hr : ∀ j, (recurrence m lam).charPoly.IsRoot (roots j)) :
    LinearMap.ker (boundaryMatrix m n roots).mulVecLin ≃ₗ[ℂ]
      Module.End.eigenspace (toeplitz m n).mulVecLin lam := by
  apply LinearEquiv.ofBijective (boundaryToEigenspace m n hm lam roots hr)
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    apply Subtype.ext
    apply boundary_kernel_restriction_injective m n roots hinj c.val c.property
    exact congrArg Subtype.val hc
  · intro v
    have hv : (toeplitz m n).mulVec v.val = lam • v.val :=
      Module.End.mem_eigenspace_iff.mp v.property
    obtain ⟨c, hc, he⟩ := eigenvector_has_geometric_representation m n hm lam roots hinj hr v.val hv
    refine ⟨⟨c, hc⟩, ?_⟩
    exact Subtype.ext he

theorem boundaryKernel_finrank (m n : ℕ) (hm : 0 < m) (lam : ℂ)
    (roots : Fin (2 * m) → ℂ) (hinj : Function.Injective roots)
    (hr : ∀ j, (recurrence m lam).charPoly.IsRoot (roots j)) :
    Module.finrank ℂ (LinearMap.ker (boundaryMatrix m n roots).mulVecLin) =
      Module.finrank ℂ (Module.End.eigenspace (toeplitz m n).mulVecLin lam) :=
  (boundaryKernelEquivEigenspace m n hm lam roots hinj hr).finrank_eq

end MF21Boundary
#print axioms MF21Boundary.finite_extension
#print axioms MF21Boundary.recurrence_at_iff

#print axioms MF21Boundary.eigenvector_iff_boundary_det_zero

#print axioms MF21Boundary.boundaryKernelEquivEigenspace
#print axioms MF21Boundary.boundaryKernel_finrank
