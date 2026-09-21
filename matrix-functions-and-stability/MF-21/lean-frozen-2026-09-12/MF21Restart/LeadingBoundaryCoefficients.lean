import MF21Restart.LeadingBoundaryIndices
import MF21Restart.RootListProducts
import MF21Restart.PhaseProduct
import Mathlib.Algebra.BigOperators.Fin

/-!
The two literal leading Laplace coefficients in manuscript (15). The
column order fixes sigma = -1. All identities are algebraic and remain
valid at the endpoints, where the full root list can have repetitions.
The statement lock is `LEADING_BOUNDARY_COEFFICIENTS_STATEMENTS.md`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

private lemma leading_vandermonde_cons (k : ℕ) (v : Fin k → ℂ) (u : ℂ) :
    (Matrix.vandermonde (Fin.cons u v)).det =
      (∏ i : Fin k, (v i - u)) * (Matrix.vandermonde v).det := by
  rw [Matrix.det_vandermonde, Fin.prod_univ_succ]
  simp only [Fin.prod_Ioi_zero, Fin.prod_Ioi_succ, Fin.cons_zero, Fin.cons_succ,
    Matrix.det_vandermonde]

private lemma leading_prod_Ioi_castSucc
    (k : ℕ) (g : Fin (k + 1) → ℂ) (i : Fin k) :
    (∏ j ∈ Finset.Ioi i.castSucc, g j) =
      g (Fin.last k) * ∏ j ∈ Finset.Ioi i, g j.castSucc := by
  have hs : Finset.Ioi i.castSucc =
      insert (Fin.last k) ((Finset.Ioi i).map Fin.castSuccEmb) := by
    rw [Fin.map_castSuccEmb_Ioi, Finset.Ioo_insert_right (by
      change i.val < k
      exact i.isLt)]
    ext j
    simp only [Finset.mem_Ioi, Finset.mem_Ioc]
    exact ⟨fun h => ⟨h, by have := j.isLt; change j.val ≤ k; omega⟩, And.left⟩
  have hn : Fin.last k ∉ (Finset.Ioi i).map Fin.castSuccEmb := by
    rw [Fin.map_castSuccEmb_Ioi]
    simp only [Finset.mem_Ioo, lt_self_iff_false, and_false, not_false_eq_true]
  rw [hs, Finset.prod_insert hn, Finset.prod_map]
  rfl

private lemma leading_vandermonde_snoc (k : ℕ) (v : Fin k → ℂ) (u : ℂ) :
    (Matrix.vandermonde (Fin.snoc v u)).det =
      (Matrix.vandermonde v).det * ∏ i : Fin k, (u - v i) := by
  rw [Matrix.det_vandermonde, Fin.prod_univ_castSucc]
  have hlast : (Finset.Ioi (Fin.last k) : Finset (Fin (k + 1))) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have hlt := Finset.mem_Ioi.mp hj
    have hbound := j.isLt
    change k < j.val at hlt
    omega
  rw [hlast, Finset.prod_empty, mul_one]
  simp_rw [leading_prod_Ioi_castSucc]
  simp only [Fin.snoc_last, Fin.snoc_castSucc]
  rw [Finset.prod_mul_distrib, ← Matrix.det_vandermonde]
  exact mul_comm _ _

private lemma leading_stable_append
    (m : ℕ) (θ : ℝ) (u : ℂ) (hu : u ≠ 0) :
    (Matrix.vandermonde (Fin.snoc (stableRootList m θ) u)).det =
      (Matrix.vandermonde (stableRootList m θ)).det * u ^ (m - 1) *
        ∏ ell : Fin (m - 1), (1 - stableRootList m θ ell * u⁻¹) := by
  rw [leading_vandermonde_snoc]
  have hprod : (∏ ell : Fin (m - 1), (u - stableRootList m θ ell)) =
      u ^ (m - 1) * ∏ ell : Fin (m - 1), (1 - stableRootList m θ ell * u⁻¹) := by
    calc
      (∏ ell : Fin (m - 1), (u - stableRootList m θ ell)) =
          ∏ ell : Fin (m - 1), u * (1 - stableRootList m θ ell * u⁻¹) := by
        apply Finset.prod_congr rfl
        intro ell _
        field_simp [hu]
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin]
  rw [hprod, mul_assoc]

private lemma leading_exterior_prepend
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (u : ℂ) :
    (Matrix.vandermonde (Fin.cons u (exteriorRootList m θ))).det =
      boundaryExteriorProduct m θ *
        (∏ ell : Fin (m - 1), (1 - stableRootList m θ ell * u)) *
        (Matrix.vandermonde (exteriorRootList m θ)).det := by
  rw [leading_vandermonde_cons]
  have hprod : (∏ ell : Fin (m - 1), (exteriorRootList m θ ell - u)) =
      boundaryExteriorProduct m θ *
        ∏ ell : Fin (m - 1), (1 - stableRootList m θ ell * u) := by
    rw [boundaryExteriorProduct_eq_prod_exteriorRootList m hm θ,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro ell _
    have hr : stableRootList m θ ell ≠ 0 := stableRootCurve_ne_zero _ _
    change (stableRootList m θ ell)⁻¹ - u =
      (stableRootList m θ ell)⁻¹ * (1 - stableRootList m θ ell * u)
    rw [mul_sub, mul_one, ← mul_assoc, inv_mul_cancel₀ hr, one_mul]
  rw [hprod]

/-- Reversing the stable-root indices under conjugation gives the actual
second phase product. No principal argument of a product is used. -/
theorem leading_phaseProduct_conj (m : ℕ) (θ : ℝ) :
    (∏ ell : Fin (m - 1), (1 - stableRootList m θ ell * oscillatoryRoot θ)) =
      (starRingEnd ℂ) (manuscriptPhaseProduct m θ) := by
  have hz : (starRingEnd ℂ) ((oscillatoryRoot θ)⁻¹) = oscillatoryRoot θ := by
    have hc : (starRingEnd ℂ) (oscillatoryRoot θ) = (oscillatoryRoot θ)⁻¹ := by
      simp only [oscillatoryRoot, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
        Complex.conj_I, mul_neg, Complex.exp_neg]
    rw [map_inv₀, hc, inv_inv]
  have hf : (starRingEnd ℂ) (manuscriptPhaseProduct m θ) =
      ∏ ell : Fin (m - 1), (1 - stableRootList m θ ell.rev * oscillatoryRoot θ) := by
    unfold manuscriptPhaseProduct
    simp only [map_prod, map_sub, map_one, map_mul, hz]
    change (∏ ell : Fin (m - 1),
      (1 - (starRingEnd ℂ) (stableRootList m θ ell) * oscillatoryRoot θ)) = _
    simp only [stableRootList_conj]
  rw [hf]
  symm
  simpa only [Fin.revPerm_apply] using
    (Equiv.prod_comp (Fin.revPerm : Equiv.Perm (Fin (m - 1)))
      (fun ell => 1 - stableRootList m θ ell * oscillatoryRoot θ))

private lemma leadingZ_selected_tuple (k : ℕ) (hm : 2 ≤ k + 1) (θ : ℝ) :
    (fun i : Fin (k + 1) => characteristicRoots (k + 1) θ
      ((boundaryLeadingZIndices (k + 1) (by omega)).orderEmbOfFin
        (card_boundaryLeadingZIndices (k + 1) (by omega)) i)) =
      Fin.cons (oscillatoryRoot θ) (exteriorRootList (k + 1) θ) := by
  let e := (boundaryLeadingZIndices (k + 1) (by omega)).orderEmbOfFin
    (card_boundaryLeadingZIndices (k + 1) (by omega))
  change (fun i => characteristicRoots (k + 1) θ (e i)) = _
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Fin.cons_zero]
    apply characteristicRoots_unit
    simpa [e] using boundaryLeadingZIndices_orderEmb_val (k + 1) (by omega) 0
  · rw [Fin.cons_succ]
    have hv : (e j.succ).val = (k + 1) + (j.val + 1) := by
      simpa [e] using boundaryLeadingZIndices_orderEmb_val (k + 1) (by omega) j.succ
    rw [characteristicRoots_exterior (k + 1) θ (e j.succ) (by rw [hv]; omega)]
    change (stableRootCurve (rootKappa (k + 1) ((e j.succ).val - (k + 1))) θ)⁻¹ =
      (stableRootCurve (rootKappa (k + 1) (j.val + 1)) θ)⁻¹
    rw [hv, show (k + 1) + (j.val + 1) - (k + 1) = j.val + 1 by omega]

private lemma leadingZInv_selected_tuple (k : ℕ) (hm : 2 ≤ k + 1) (θ : ℝ) :
    (fun i : Fin (k + 1) => characteristicRoots (k + 1) θ
      ((boundaryLeadingZInvIndices (k + 1) (by omega)).orderEmbOfFin
        (card_boundaryLeadingZInvIndices (k + 1) (by omega)) i)) =
      Fin.cons ((oscillatoryRoot θ)⁻¹) (exteriorRootList (k + 1) θ) := by
  let e := (boundaryLeadingZInvIndices (k + 1) (by omega)).orderEmbOfFin
    (card_boundaryLeadingZInvIndices (k + 1) (by omega))
  change (fun i => characteristicRoots (k + 1) θ (e i)) = _
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Fin.cons_zero]
    apply characteristicRoots_unit_inv (k + 1) hm
    simpa [e] using boundaryLeadingZInvIndices_orderEmb_val (k + 1) (by omega) 0
  · rw [Fin.cons_succ]
    have hv : (e j.succ).val = (k + 1) + (j.val + 1) := by
      simpa [e] using boundaryLeadingZInvIndices_orderEmb_val (k + 1) (by omega) j.succ
    rw [characteristicRoots_exterior (k + 1) θ (e j.succ) (by rw [hv]; omega)]
    change (stableRootCurve (rootKappa (k + 1) ((e j.succ).val - (k + 1))) θ)⁻¹ =
      (stableRootCurve (rootKappa (k + 1) (j.val + 1)) θ)⁻¹
    rw [hv, show (k + 1) + (j.val + 1) - (k + 1) = j.val + 1 by omega]

private lemma leadingZ_complement_tuple (k : ℕ) (hm : 2 ≤ k + 1) (θ : ℝ) :
    (fun i : Fin (k + 1) => characteristicRoots (k + 1) θ
      ((boundaryLeadingZIndices (k + 1) (by omega))ᶜ.orderEmbOfFin
        (boundary_compl_card (card_boundaryLeadingZIndices (k + 1) (by omega))) i)) =
      Fin.snoc (stableRootList (k + 1) θ) ((oscillatoryRoot θ)⁻¹) := by
  let e := (boundaryLeadingZIndices (k + 1) (by omega))ᶜ.orderEmbOfFin
    (boundary_compl_card (card_boundaryLeadingZIndices (k + 1) (by omega)))
  change (fun i => characteristicRoots (k + 1) θ (e i)) = _
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last]
    apply characteristicRoots_unit_inv (k + 1) hm
    simpa [e] using
      boundaryLeadingZIndices_compl_orderEmb_val (k + 1) (by omega) (Fin.last k)
  · rw [Fin.snoc_castSucc]
    have hj : j.val ≠ k := by have := j.isLt; omega
    have hv : (e j.castSucc).val = j.val := by
      simpa [e, hj] using
        boundaryLeadingZIndices_compl_orderEmb_val (k + 1) (by omega) j.castSucc
    rw [characteristicRoots_stable (k + 1) θ (e j.castSucc) (by
      rw [hv]
      simpa using j.isLt)]
    change stableRootCurve (rootKappa (k + 1) ((e j.castSucc).val + 1)) θ =
      stableRootCurve (rootKappa (k + 1) (j.val + 1)) θ
    rw [hv]

private lemma leadingZInv_complement_tuple (k : ℕ) (hm : 2 ≤ k + 1) (θ : ℝ) :
    (fun i : Fin (k + 1) => characteristicRoots (k + 1) θ
      ((boundaryLeadingZInvIndices (k + 1) (by omega))ᶜ.orderEmbOfFin
        (boundary_compl_card (card_boundaryLeadingZInvIndices (k + 1) (by omega))) i)) =
      Fin.snoc (stableRootList (k + 1) θ) (oscillatoryRoot θ) := by
  let e := (boundaryLeadingZInvIndices (k + 1) (by omega))ᶜ.orderEmbOfFin
    (boundary_compl_card (card_boundaryLeadingZInvIndices (k + 1) (by omega)))
  change (fun i => characteristicRoots (k + 1) θ (e i)) = _
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last]
    apply characteristicRoots_unit
    simpa [e] using
      boundaryLeadingZInvIndices_compl_orderEmb_val (k + 1) (by omega) (Fin.last k)
  · rw [Fin.snoc_castSucc]
    have hv : (e j.castSucc).val = j.val := by
      simpa [e] using
        boundaryLeadingZInvIndices_compl_orderEmb_val (k + 1) (by omega) j.castSucc
    rw [characteristicRoots_stable (k + 1) θ (e j.castSucc) (by
      rw [hv]
      simpa using j.isLt)]
    change stableRootCurve (rootKappa (k + 1) ((e j.castSucc).val + 1)) θ =
      stableRootCurve (rootKappa (k + 1) (j.val + 1)) θ
    rw [hv]

/-- The plus coefficient in (15), with the actual inherited-order sign -1. -/
theorem boundaryCoefficient_leadingZ (m : ℕ) (hm : 2 ≤ m) (θ : ℝ) :
    boundaryCoefficient m (characteristicRoots m θ)
        (boundaryLeadingZIndices m (by omega)) =
      -((Matrix.vandermonde (stableRootList m θ)).det *
        (Matrix.vandermonde (exteriorRootList m θ)).det *
        boundaryExteriorProduct m θ * (oscillatoryRoot θ)⁻¹ ^ (m - 1) *
        ((starRingEnd ℂ) (manuscriptPhaseProduct m θ)) ^ 2) := by
  cases m with
  | zero => omega
  | succ k =>
    rw [boundaryCoefficient_vandermonde _ _ _ (card_boundaryLeadingZIndices _ (by omega)),
      boundaryLaplaceSign_leadingZ, leadingZ_complement_tuple k hm θ,
      leadingZ_selected_tuple k hm θ,
      leading_stable_append _ θ _ (inv_ne_zero (oscillatoryRoot_ne_zero θ)),
      leading_exterior_prepend _ (by omega) θ]
    simp only [inv_inv, leading_phaseProduct_conj]
    norm_num <;> ring

/-- The minus coefficient in (15); the two coefficients have opposite signs. -/
theorem boundaryCoefficient_leadingZInv (m : ℕ) (hm : 2 ≤ m) (θ : ℝ) :
    boundaryCoefficient m (characteristicRoots m θ)
        (boundaryLeadingZInvIndices m (by omega)) =
      (Matrix.vandermonde (stableRootList m θ)).det *
        (Matrix.vandermonde (exteriorRootList m θ)).det *
        boundaryExteriorProduct m θ * (oscillatoryRoot θ) ^ (m - 1) *
        (manuscriptPhaseProduct m θ) ^ 2 := by
  cases m with
  | zero => omega
  | succ k =>
    rw [boundaryCoefficient_vandermonde _ _ _
        (card_boundaryLeadingZInvIndices _ (by omega)),
      boundaryLaplaceSign_leadingZInv, leadingZInv_complement_tuple k hm θ,
      leadingZInv_selected_tuple k hm θ,
      leading_stable_append _ θ _ (oscillatoryRoot_ne_zero θ),
      leading_exterior_prepend _ (by omega) θ]
    change (↑↑(1 : ℤˣ) : ℂ) *
      ((Matrix.vandermonde (stableRootList (k + 1) θ)).det *
        (oscillatoryRoot θ) ^ k * manuscriptPhaseProduct (k + 1) θ) *
      (boundaryExteriorProduct (k + 1) θ * manuscriptPhaseProduct (k + 1) θ *
        (Matrix.vandermonde (exteriorRootList (k + 1) θ)).det) = _
    norm_num <;> ring

theorem boundaryLeadingZIndices_rootProduct (m : ℕ) (hm : 2 ≤ m) (θ : ℝ) :
    (∏ i ∈ boundaryLeadingZIndices m (by omega), characteristicRoots m θ i) =
      oscillatoryRoot θ * boundaryExteriorProduct m θ := by
  have hn : (⟨m - 1, by omega⟩ : Fin (2 * m)) ∉ boundaryExteriorIndices m := by
    rw [mem_boundaryExteriorIndices]
    change ¬m < m - 1
    omega
  rw [boundaryLeadingZIndices, Finset.prod_insert hn,
    characteristicRoots_unit m θ _ rfl]
  rfl

theorem boundaryLeadingZInvIndices_rootProduct (m : ℕ) (hm : 2 ≤ m) (θ : ℝ) :
    (∏ i ∈ boundaryLeadingZInvIndices m (by omega), characteristicRoots m θ i) =
      (oscillatoryRoot θ)⁻¹ * boundaryExteriorProduct m θ := by
  have hn : (⟨m, by omega⟩ : Fin (2 * m)) ∉ boundaryExteriorIndices m := by
    rw [mem_boundaryExteriorIndices]
    change ¬m < m
    omega
  rw [boundaryLeadingZInvIndices, Finset.prod_insert hn,
    characteristicRoots_unit_inv m hm θ _ rfl]
  rfl

#print axioms leading_phaseProduct_conj
#print axioms boundaryCoefficient_leadingZ
#print axioms boundaryCoefficient_leadingZInv
#print axioms boundaryLeadingZIndices_rootProduct
#print axioms boundaryLeadingZInvIndices_rootProduct

end MF21Restart
