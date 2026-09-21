import MF21Restart.BoundaryProductDecay
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

def stableRootList (m : ℕ) (θ : ℝ) (ell : Fin (m - 1)) : ℂ :=
  stableRootCurve (rootKappa m (ell.val + 1)) θ

def exteriorRootList (m : ℕ) (θ : ℝ) (ell : Fin (m - 1)) : ℂ :=
  (stableRootList m θ ell)⁻¹

theorem stableRootList_conj (m : ℕ) (θ : ℝ) (ell : Fin (m - 1)) :
    (starRingEnd ℂ) (stableRootList m θ ell) = stableRootList m θ ell.rev := by
  have hi := ell.isLt
  have he : m - (ell.val + 1) = ell.rev.val + 1 := by
    rw [Fin.val_rev]
    omega
  unfold stableRootList
  rw [stableRootCurve_rootKappa_conj m (ell.val + 1) (by omega) (by omega), he]

theorem exteriorRootList_conj (m : ℕ) (θ : ℝ) (ell : Fin (m - 1)) :
    (starRingEnd ℂ) (exteriorRootList m θ ell) = exteriorRootList m θ ell.rev := by
  simp only [exteriorRootList, map_inv₀, stableRootList_conj]

theorem boundaryExteriorProduct_eq_prod_exteriorRootList (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) :
    boundaryExteriorProduct m θ = ∏ ell : Fin (m - 1), exteriorRootList m θ ell := by
  classical
  let f : Fin (m - 1) → Fin (2 * m) := fun ell => ⟨m + 1 + ell.val, by have := ell.isLt; omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hval := congrArg Fin.val hab
    dsimp [f] at hval
    exact Fin.ext (by omega)
  have hE : boundaryExteriorIndices m = Finset.univ.image f := by
    ext i
    simp only [mem_boundaryExteriorIndices, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hi
      refine ⟨⟨i.val - (m + 1), by have := i.isLt; omega⟩, ?_⟩
      apply Fin.ext
      dsimp [f]
      omega
    · rintro ⟨ell, rfl⟩
      dsimp [f]
      omega
  unfold boundaryExteriorProduct
  rw [hE, Finset.prod_image (fun a _ b _ hab => hf hab)]
  apply Finset.prod_congr rfl
  intro ell _
  rw [characteristicRoots_exterior m θ (f ell) (by dsimp [f]; omega)]
  change (stableRootCurve (rootKappa m (m + 1 + ell.val - m)) θ)⁻¹ = _
  rw [show m + 1 + ell.val - m = ell.val + 1 by omega]
  rfl

theorem boundaryExteriorProduct_conj (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) :
    (starRingEnd ℂ) (boundaryExteriorProduct m θ) = boundaryExteriorProduct m θ := by
  rw [boundaryExteriorProduct_eq_prod_exteriorRootList m hm θ]
  simp only [map_prod, exteriorRootList_conj]
  simpa only [Fin.revPerm_apply] using
    (Equiv.prod_comp (Fin.revPerm : Equiv.Perm (Fin (m - 1))) (exteriorRootList m θ))

theorem boundaryExteriorProduct_zero (m : ℕ) (hm : 1 ≤ m) :
    boundaryExteriorProduct m 0 = 1 := by
  rw [boundaryExteriorProduct_eq_prod_exteriorRootList m hm 0]
  simp only [exteriorRootList, stableRootList, stableRootCurve_zero, inv_one, Finset.prod_const_one]

theorem boundaryExteriorProduct_re_pos (m : ℕ) (hm : 2 ≤ m) (θ : ℝ) (hθ : 0 ≤ θ) :
    0 < (boundaryExteriorProduct m θ).re := by
  have hm1 : 1 ≤ m := by omega
  have hn (t : ℝ) : (boundaryExteriorProduct m t).re ≠ 0 := by
    intro hzero
    apply boundaryExteriorProduct_ne_zero m t
    rw [← Complex.conj_eq_iff_re.mp (boundaryExteriorProduct_conj m hm1 t), hzero,
      Complex.ofReal_zero]
  have hc : Continuous (fun t : ℝ => (boundaryExteriorProduct m t).re) :=
    Complex.continuous_re.comp (boundaryExteriorProduct_contDiff m hm).continuous
  by_contra hnot
  have hle : (boundaryExteriorProduct m θ).re ≤ 0 := le_of_not_gt hnot
  have hzero : 0 ≤ (boundaryExteriorProduct m 0).re := by
    rw [boundaryExteriorProduct_zero m hm1]
    norm_num
  obtain ⟨t, ht, hval⟩ := intermediate_value_Icc' hθ hc.continuousOn ⟨hle, hzero⟩
  exact hn t hval

theorem vandermonde_conj_of_reverse (k : ℕ) (v : Fin k → ℂ)
    (hv : ∀ i, (starRingEnd ℂ) (v i) = v i.rev) :
    (starRingEnd ℂ) (Matrix.vandermonde v).det =
      (↑↑(Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin k))) : ℂ) *
        (Matrix.vandermonde v).det := by
  have hmap : (Matrix.vandermonde v).map (starRingEnd ℂ) =
      (Matrix.vandermonde v).submatrix Fin.revPerm id := by
    ext i j
    simp only [Matrix.map_apply, Matrix.vandermonde_apply, map_pow, hv,
      Matrix.submatrix_apply, id_eq, Fin.revPerm_apply]
  rw [RingHom.map_det]
  change ((Matrix.vandermonde v).map (starRingEnd ℂ)).det = _
  rw [hmap, Matrix.det_permute]

theorem rootVandermondeProduct_conj (m : ℕ) (θ : ℝ) :
    (starRingEnd ℂ)
        ((Matrix.vandermonde (stableRootList m θ)).det *
          (Matrix.vandermonde (exteriorRootList m θ)).det) =
      (Matrix.vandermonde (stableRootList m θ)).det *
        (Matrix.vandermonde (exteriorRootList m θ)).det := by
  rw [map_mul, vandermonde_conj_of_reverse _ _ (stableRootList_conj m θ),
    vandermonde_conj_of_reverse _ _ (exteriorRootList_conj m θ)]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m - 1))))
      with h | h <;> simp [h]

#print axioms stableRootList_conj
#print axioms exteriorRootList_conj
#print axioms boundaryExteriorProduct_eq_prod_exteriorRootList
#print axioms boundaryExteriorProduct_conj
#print axioms boundaryExteriorProduct_zero
#print axioms boundaryExteriorProduct_re_pos
#print axioms rootVandermondeProduct_conj

end MF21Restart
