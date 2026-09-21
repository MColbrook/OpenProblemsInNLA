import MF21Restart.ConcreteBoundary
import MF21Restart.StableRootBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Order.Interval.Finset.Fin

/-!
The actual subset-product ratio in manuscript (17). Selected exterior factors
cancel against Q; every nonleading subset leaves either a selected stable
factor or the reciprocal of an omitted exterior factor. No coefficient or
determinant estimate is assumed here.

See `BOUNDARY_PRODUCT_DECAY_STATEMENTS.md` for the statement-first lock.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

def boundaryExteriorIndices (m : ℕ) : Finset (Fin (2 * m)) :=
  Finset.univ.filter (fun i => m < i.val)

def boundaryLeadingZIndices (m : ℕ) (hm : 1 ≤ m) : Finset (Fin (2 * m)) :=
  insert ⟨m - 1, by omega⟩ (boundaryExteriorIndices m)

def boundaryLeadingZInvIndices (m : ℕ) (hm : 1 ≤ m) : Finset (Fin (2 * m)) :=
  insert ⟨m, by omega⟩ (boundaryExteriorIndices m)

def boundaryExteriorProduct (m : ℕ) (θ : ℝ) : ℂ :=
  ∏ i ∈ boundaryExteriorIndices m, characteristicRoots m θ i

def boundaryProductRatio (m : ℕ) (θ : ℝ) (S : Finset (Fin (2 * m))) : ℂ :=
  (∏ i ∈ S, characteristicRoots m θ i) / boundaryExteriorProduct m θ

@[simp]
lemma mem_boundaryExteriorIndices (m : ℕ) (i : Fin (2 * m)) :
    i ∈ boundaryExteriorIndices m ↔ m < i.val := by
  simp only [boundaryExteriorIndices, Finset.mem_filter, Finset.mem_univ, true_and]

lemma card_boundaryExteriorIndices (m : ℕ) (hm : 1 ≤ m) :
    (boundaryExteriorIndices m).card = m - 1 := by
  let i : Fin (2 * m) := ⟨m, by omega⟩
  have heq : boundaryExteriorIndices m = Finset.Ioi i := by
    ext j
    simp [boundaryExteriorIndices, i, Fin.lt_def]
  rw [heq, Fin.card_Ioi]
  dsimp [i]
  omega

theorem card_boundaryLeadingZIndices (m : ℕ) (hm : 1 ≤ m) :
    (boundaryLeadingZIndices m hm).card = m := by
  have hn : (⟨m - 1, by omega⟩ : Fin (2 * m)) ∉ boundaryExteriorIndices m := by
    simp only [mem_boundaryExteriorIndices]
    omega
  rw [boundaryLeadingZIndices, Finset.card_insert_of_notMem hn,
    card_boundaryExteriorIndices m hm]
  omega

theorem boundaryLeadingZIndices_separates (m : ℕ) (hm : 1 ≤ m)
    (a b : Fin (2 * m)) (ha : a.val = m - 1) (hb : b.val = m) :
    a ∈ boundaryLeadingZIndices m hm ↔ b ∉ boundaryLeadingZIndices m hm := by
  have ha' : a = ⟨m - 1, by omega⟩ := Fin.ext ha
  have hb' : b ≠ (⟨m - 1, by omega⟩ : Fin (2 * m)) := by
    intro h
    have := congrArg Fin.val h
    simp only [hb] at this
    omega
  simp [boundaryLeadingZIndices, ha', hb', mem_boundaryExteriorIndices, hb]

theorem boundaryExteriorProduct_ne_zero (m : ℕ) (θ : ℝ) :
    boundaryExteriorProduct m θ ≠ 0 := by
  unfold boundaryExteriorProduct
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => characteristicRoots_ne_zero m θ i)

theorem boundaryProductRatio_ne_zero (m : ℕ) (θ : ℝ) (S : Finset (Fin (2 * m))) :
    boundaryProductRatio m θ S ≠ 0 := by
  unfold boundaryProductRatio
  exact div_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun i _ => characteristicRoots_ne_zero m θ i))
    (boundaryExteriorProduct_ne_zero m θ)

theorem boundaryExteriorProduct_contDiff (m : ℕ) (hm : 2 ≤ m) :
    ContDiff ℝ ⊤ (boundaryExteriorProduct m) := by
  unfold boundaryExteriorProduct
  exact contDiff_prod (fun i _ => characteristicRoots_contDiff m hm i)

theorem boundaryProductRatio_contDiff (m : ℕ) (hm : 2 ≤ m)
    (S : Finset (Fin (2 * m))) :
    ContDiff ℝ ⊤ (fun θ : ℝ => boundaryProductRatio m θ S) := by
  have hnum : ContDiff ℝ ⊤ (fun θ : ℝ => ∏ i ∈ S, characteristicRoots m θ i) :=
    contDiff_prod (fun i _ => characteristicRoots_contDiff m hm i)
  convert! hnum.mul ((boundaryExteriorProduct_contDiff m hm).inv
    (boundaryExteriorProduct_ne_zero m)) using 1 <;>
    simp only [boundaryProductRatio, div_eq_mul_inv]

/-- Cardinality alone identifies the exceptional subsets when no stable root
is selected and no exterior root is omitted. The statement concerns indices,
so it remains valid when the two unit-root values coincide at theta=pi. -/
theorem boundary_nonleading_has_stable_or_omitted_exterior
    (m : ℕ) (hm : 1 ≤ m) (S : Finset (Fin (2 * m))) (hcard : S.card = m)
    (hZ : S ≠ boundaryLeadingZIndices m hm)
    (hZInv : S ≠ boundaryLeadingZInvIndices m hm) :
    (∃ i ∈ S, i.val < m - 1) ∨
      (∃ i ∈ boundaryExteriorIndices m, i ∉ S) := by
  classical
  by_cases hstable : ∃ i ∈ S, i.val < m - 1
  · exact Or.inl hstable
  right
  by_contra homitted
  have hsub : boundaryExteriorIndices m ⊆ S := by
    intro i hi
    by_contra hiS
    exact homitted ⟨i, hi, hiS⟩
  have hdiff : (S \ boundaryExteriorIndices m).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hcard, card_boundaryExteriorIndices m hm]
    omega
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hdiff
  have himem : i ∈ S \ boundaryExteriorIndices m := by
    rw [hi]
    exact Finset.mem_singleton_self i
  have hiS : i ∈ S := (Finset.mem_sdiff.mp himem).1
  have hiE : ¬m < i.val := by
    simpa only [mem_boundaryExteriorIndices] using (Finset.mem_sdiff.mp himem).2
  have hiStable : ¬i.val < m - 1 := fun h => hstable ⟨i, hiS, h⟩
  have hS : S = insert i (boundaryExteriorIndices m) := by
    calc
      S = (S \ boundaryExteriorIndices m) ∪ boundaryExteriorIndices m :=
        (Finset.sdiff_union_of_subset hsub).symm
      _ = {i} ∪ boundaryExteriorIndices m := by rw [hi]
      _ = insert i (boundaryExteriorIndices m) := Finset.singleton_union _ _
  have hpos : i.val = m - 1 ∨ i.val = m := by omega
  rcases hpos with hiz | hizinv
  · apply hZ
    rw [hS]
    unfold boundaryLeadingZIndices
    congr 1
    exact Fin.ext hiz
  · apply hZInv
    rw [hS]
    unfold boundaryLeadingZInvIndices
    congr 1
    exact Fin.ext hizinv

/-- The selected exterior roots cancel exactly. No exterior-root norm is
incorrectly bounded by one; only reciprocals of omitted exterior roots remain. -/
theorem boundaryProductRatio_eq_sdiff_prod
    (m : ℕ) (θ : ℝ) (S : Finset (Fin (2 * m))) :
    boundaryProductRatio m θ S =
      (∏ i ∈ S \ boundaryExteriorIndices m, characteristicRoots m θ i) *
        ∏ i ∈ boundaryExteriorIndices m \ S, (characteristicRoots m θ i)⁻¹ := by
  classical
  let E := boundaryExteriorIndices m
  let w := characteristicRoots m θ
  have hcommon : (∏ i ∈ S ∩ E, w i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => characteristicRoots_ne_zero m θ i)
  change (∏ i ∈ S, w i) / (∏ i ∈ E, w i) =
    (∏ i ∈ S \ E, w i) * ∏ i ∈ E \ S, (w i)⁻¹
  rw [← Finset.prod_inter_mul_prod_sdiff S E w,
    ← Finset.prod_inter_mul_prod_sdiff E S w,
    Finset.inter_comm E S, mul_div_mul_left _ _ hcommon,
    div_eq_mul_inv, Finset.prod_inv_distrib]

theorem boundaryProductRatio_norm_eq_sdiff_prod
    (m : ℕ) (θ : ℝ) (S : Finset (Fin (2 * m))) :
    ‖boundaryProductRatio m θ S‖ =
      (∏ i ∈ S \ boundaryExteriorIndices m, ‖characteristicRoots m θ i‖) *
        ∏ i ∈ boundaryExteriorIndices m \ S, ‖(characteristicRoots m θ i)⁻¹‖ := by
  rw [boundaryProductRatio_eq_sdiff_prod, norm_mul, norm_prod, norm_prod]

private lemma prod_le_selected_factor {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (i : ι) (hi : i ∈ s) (h0 : ∀ j ∈ s, 0 ≤ f j) (h1 : ∀ j ∈ s, f j ≤ 1) :
    ∏ j ∈ s, f j ≤ f i := by
  classical
  simpa only [Finset.prod_singleton] using
    (Finset.prod_le_prod_of_subset_of_le_one
      (Finset.singleton_subset_iff.mpr hi) h0 (fun j hj _ => h1 j hj))

theorem boundaryProductRatio_uniform_exp_decay (m : ℕ) (hm : 2 ≤ m) :
    ∃ c : ℝ, 0 < c ∧
      ∀ S : Finset (Fin (2 * m)), S.card = m →
        S ≠ boundaryLeadingZIndices m (by omega) →
        S ≠ boundaryLeadingZInvIndices m (by omega) →
        ∀ θ : ℝ, 0 ≤ θ → θ ≤ Real.pi →
          ‖boundaryProductRatio m θ S‖ ≤ Real.exp (-c * θ) := by
  classical
  obtain ⟨c, hc, hroots⟩ := stable_roots_uniform_exp_decay m hm
  refine ⟨c, hc, ?_⟩
  intro S hcard hZ hZInv θ hθ hθπ
  have hexp : Real.exp (-c * θ) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hstableOne (ell : ℕ) (hell : 1 ≤ ell) (hellm : ell < m) :
      ‖stableRootCurve (rootKappa m ell) θ‖ ≤ 1 :=
    (hroots ell hell hellm θ hθ hθπ).trans hexp
  have hnonexterior (i : Fin (2 * m)) (hi : i ∉ boundaryExteriorIndices m) :
      ‖characteristicRoots m θ i‖ ≤ 1 := by
    have him : i.val ≤ m := by
      have h := mt (mem_boundaryExteriorIndices m i).mpr hi
      omega
    by_cases hs : i.val < m - 1
    · rw [characteristicRoots_stable m θ i hs]
      exact hstableOne (i.val + 1) (by omega) (by omega)
    · have hmiddle : i.val = m - 1 ∨ i.val = m := by omega
      rcases hmiddle with hz | hzinv
      · rw [characteristicRoots_unit m θ i hz]
        exact (oscillatoryRoot_norm θ).le
      · simpa only [characteristicRoots_unit_inv m hm θ i hzinv, norm_inv,
          oscillatoryRoot_norm, inv_one] using (le_refl (1 : ℝ))
  have hexterior (i : Fin (2 * m)) (hi : i ∈ boundaryExteriorIndices m) :
      ‖(characteristicRoots m θ i)⁻¹‖ ≤ Real.exp (-c * θ) := by
    have him := (mem_boundaryExteriorIndices m i).mp hi
    have hibound := i.isLt
    rw [characteristicRoots_exterior m θ i him, inv_inv]
    exact hroots (i.val - m) (by omega) (by omega) θ hθ hθπ
  let a : Fin (2 * m) → ℝ := fun i => ‖characteristicRoots m θ i‖
  let b : Fin (2 * m) → ℝ := fun i => ‖(characteristicRoots m θ i)⁻¹‖
  have ha0 : ∀ i ∈ S \ boundaryExteriorIndices m, 0 ≤ a i := fun _ _ => norm_nonneg _
  have hb0 : ∀ i ∈ boundaryExteriorIndices m \ S, 0 ≤ b i := fun _ _ => norm_nonneg _
  have ha1 : ∀ i ∈ S \ boundaryExteriorIndices m, a i ≤ 1 :=
    fun i hi => hnonexterior i (Finset.mem_sdiff.mp hi).2
  have hb1 : ∀ i ∈ boundaryExteriorIndices m \ S, b i ≤ 1 :=
    fun i hi => (hexterior i (Finset.mem_sdiff.mp hi).1).trans hexp
  have hA1 : (∏ i ∈ S \ boundaryExteriorIndices m, a i) ≤ 1 := Finset.prod_le_one ha0 ha1
  have hB1 : (∏ i ∈ boundaryExteriorIndices m \ S, b i) ≤ 1 := Finset.prod_le_one hb0 hb1
  rw [boundaryProductRatio_norm_eq_sdiff_prod]
  change (∏ i ∈ S \ boundaryExteriorIndices m, a i) *
    (∏ i ∈ boundaryExteriorIndices m \ S, b i) ≤ Real.exp (-c * θ)
  rcases boundary_nonleading_has_stable_or_omitted_exterior m (by omega) S hcard hZ hZInv with
    ⟨i, hiS, hiStable⟩ | ⟨i, hiE, hiS⟩
  · have hi : i ∈ S \ boundaryExteriorIndices m := by
      apply Finset.mem_sdiff.mpr
      refine ⟨hiS, ?_⟩
      simp only [mem_boundaryExteriorIndices]
      omega
    calc
      (∏ j ∈ S \ boundaryExteriorIndices m, a j) *
          (∏ j ∈ boundaryExteriorIndices m \ S, b j) ≤
          ∏ j ∈ S \ boundaryExteriorIndices m, a j :=
        mul_le_of_le_one_right (Finset.prod_nonneg ha0) hB1
      _ ≤ a i := prod_le_selected_factor _ a i hi ha0 ha1
      _ ≤ Real.exp (-c * θ) := by
        dsimp [a]
        rw [characteristicRoots_stable m θ i hiStable]
        exact hroots (i.val + 1) (by omega) (by omega) θ hθ hθπ
  · have hi : i ∈ boundaryExteriorIndices m \ S := Finset.mem_sdiff.mpr ⟨hiE, hiS⟩
    calc
      (∏ j ∈ S \ boundaryExteriorIndices m, a j) *
          (∏ j ∈ boundaryExteriorIndices m \ S, b j) ≤
          ∏ j ∈ boundaryExteriorIndices m \ S, b j :=
        mul_le_of_le_one_left (Finset.prod_nonneg hb0) hA1
      _ ≤ b i := prod_le_selected_factor _ b i hi hb0 hb1
      _ ≤ Real.exp (-c * θ) := hexterior i hiE

#print axioms boundaryExteriorProduct_ne_zero
#print axioms boundaryProductRatio_ne_zero
#print axioms boundaryProductRatio_contDiff
#print axioms boundary_nonleading_has_stable_or_omitted_exterior
#print axioms boundaryProductRatio_eq_sdiff_prod
#print axioms boundaryProductRatio_uniform_exp_decay

end MF21Restart
