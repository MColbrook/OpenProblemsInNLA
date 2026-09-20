import MF21.BoundaryExpansion
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! The combinatorial loss in every nonleading boundary term. -/
noncomputable section
open scoped BigOperators
open Finset
namespace MF21Normalization

/-- If an m-column selection is neither dominant selection, it contains a
non-unit interior root or omits a non-unit exterior root. -/
theorem nonleading_has_loss (m : ℕ) (i₀ : Fin m)
    (S : Finset (Fin m ⊕ Fin m)) (hcard : S.card = m)
    (hP : ¬∀ j ∈ S, j.isRight)
    (hQ : ¬∀ j ∈ S, (Equiv.swap (Sum.inl i₀) (Sum.inr i₀) j).isRight) :
    ∃ j : Fin m, j ≠ i₀ ∧ (j ∈ S.toLeft ∨ j ∉ S.toRight) := by
  classical
  by_contra h
  push Not at h
  have hleft : ∀ j ∈ S.toLeft, j = i₀ := by
    intro j hj
    by_contra hji
    exact (h j hji).1 hj
  have hright : ∀ j, j ≠ i₀ → j ∈ S.toRight := by
    intro j hj
    exact (h j hj).2
  have hmem : i₀ ∈ S.toLeft := by
    by_contra hn
    apply hP
    intro j hj
    cases j with
    | inl j =>
      have he := hleft j (by simpa using hj)
      subst j
      exact (hn (by simpa using hj)).elim
    | inr j => simp
  have hSL : S.toLeft = {i₀} := by
    ext j
    simp only [mem_singleton]
    exact ⟨hleft j, fun he => he ▸ hmem⟩
  have hnright : i₀ ∉ S.toRight := by
    intro hi
    have he : S.toRight = univ := by
      ext j
      simp only [mem_univ, iff_true]
      by_cases hj : j=i₀
      · simpa [hj] using hi
      · exact hright j hj
    have hc := S.card_toLeft_add_card_toRight
    rw [hSL, he, card_singleton, card_univ, Fintype.card_fin, hcard] at hc
    omega
  apply hQ
  intro j hj
  cases j with
  | inl j =>
    have he := hleft j (by simpa using hj)
    simp [he]
  | inr j =>
    have hji : j ≠ i₀ := by
      intro he
      exact hnright (by simpa [he] using hj)
    rw [Equiv.swap_apply_of_ne_of_ne
      (show (Sum.inr j : Fin m ⊕ Fin m) ≠ Sum.inl i₀ by simp)
      (show (Sum.inr j : Fin m ⊕ Fin m) ≠ Sum.inr i₀ by simpa using hji)]
    rfl

/-- Cancellation of included exterior factors leaves precisely the selected
interior factors and omitted exterior factors. -/
theorem paired_product_ratio (m : ℕ) (r : Fin m → ℝ) (hr : ∀ j, r j ≠ 0)
    (S : Finset (Fin m ⊕ Fin m)) :
    (∏ j ∈ S, Sum.elim r (fun i => (r i)⁻¹) j) / (∏ i : Fin m, (r i)⁻¹) =
      (∏ i ∈ S.toLeft, r i) * ∏ i ∈ S.toRightᶜ, r i := by
  classical
  rw [prod_sum_eq_prod_toLeft_mul_prod_toRight]
  simp only [Sum.elim_inl, Sum.elim_inr, prod_inv_distrib]
  have hc := prod_mul_prod_compl S.toRight r
  have hn : (∏ i ∈ S.toRight, r i) ≠ 0 := prod_ne_zero_iff.mpr (fun i _ => hr i)
  rw [div_inv_eq_mul, ← hc]
  field_simp

/-- Uniform scalar loss, independent of the particular permutation. -/
theorem nonleading_product_ratio_le (m : ℕ) (i₀ : Fin m)
    (r : Fin m → ℝ) (hr0 : ∀ j, 0 < r j) (hr1 : ∀ j, r j ≤ 1)
    (ρ : ℝ) (hrρ : ∀ j, j ≠ i₀ → r j ≤ ρ)
    (S : Finset (Fin m ⊕ Fin m)) (hcard : S.card = m)
    (hP : ¬∀ j ∈ S, j.isRight)
    (hQ : ¬∀ j ∈ S, (Equiv.swap (Sum.inl i₀) (Sum.inr i₀) j).isRight) :
    (∏ j ∈ S, Sum.elim r (fun i => (r i)⁻¹) j) / (∏ i : Fin m, (r i)⁻¹) ≤ ρ := by
  classical
  rw [paired_product_ratio m r (fun j => ne_of_gt (hr0 j)) S]
  obtain ⟨j, hj, hl | hr⟩ := nonleading_has_loss m i₀ S hcard hP hQ
  · have hbound : (∏ i ∈ S.toLeft, r i) ≤ r j := by
      simpa using prod_le_prod_of_subset_of_le_one (singleton_subset_iff.mpr hl)
        (fun i _ => (hr0 i).le) (fun i _ _ => hr1 i)
    calc
      _ ≤ (∏ i ∈ S.toLeft, r i) := mul_le_of_le_one_right
        (prod_nonneg (fun i _ => (hr0 i).le))
        (prod_le_one (fun i _ => (hr0 i).le) (fun i _ => hr1 i))
      _ ≤ r j := hbound
      _ ≤ ρ := hrρ j hj
  · have hbound : (∏ i ∈ S.toRightᶜ, r i) ≤ r j := by
      simpa using prod_le_prod_of_subset_of_le_one (singleton_subset_iff.mpr (by simpa using hr))
        (fun i _ => (hr0 i).le) (fun i _ _ => hr1 i)
    calc
      _ ≤ (∏ i ∈ S.toRightᶜ, r i) := mul_le_of_le_one_left
        (prod_nonneg (fun i _ => (hr0 i).le))
        (prod_le_one (fun i _ => (hr0 i).le) (fun i _ => hr1 i))
      _ ≤ r j := hbound
      _ ≤ ρ := hrρ j hj


def selectedColumns (m : ℕ) (σ : Equiv.Perm (Fin m ⊕ Fin m)) :
    Finset (Fin m ⊕ Fin m) := univ.image (fun i : Fin m => σ (Sum.inr i))

theorem selectedColumns_card (m : ℕ) (σ : Equiv.Perm (Fin m ⊕ Fin m)) :
    (selectedColumns m σ).card = m := by
  classical
  rw [selectedColumns, card_image_of_injective]
  · exact Fintype.card_fin m
  · exact σ.injective.comp Sum.inr_injective

@[simp] theorem selectedColumns_forall (m : ℕ) (σ : Equiv.Perm (Fin m ⊕ Fin m))
    (P : Fin m ⊕ Fin m → Prop) :
    (∀ j ∈ selectedColumns m σ, P j) ↔ selects m P σ := by
  classical
  simp [selectedColumns, selects]

/-- The geometric ratio for a reciprocal root family obeys the exact same
loss estimate, with all complex phases removed by the norm. -/
theorem nonleading_base_ratio_norm_le (m : ℕ) (i₀ : Fin m)
    (z : Fin m → ℂ) (hz : ∀ j, z j ≠ 0) (hz1 : ∀ j, ‖z j‖ ≤ 1)
    (ρ : ℝ) (hzρ : ∀ j, j ≠ i₀ → ‖z j‖ ≤ ρ)
    (σ : Equiv.Perm (Fin m ⊕ Fin m))
    (hP : ¬selects m (fun j => j.isRight) σ)
    (hQ : ¬selects m (fun j => (Equiv.swap (Sum.inl i₀) (Sum.inr i₀) j).isRight) σ) :
    ‖permutationBase m (Sum.elim z (fun i => (z i)⁻¹)) σ /
      (∏ i : Fin m, (z i)⁻¹)‖ ≤ ρ := by
  classical
  have hp : permutationBase m (Sum.elim z (fun i => (z i)⁻¹)) σ =
      ∏ j ∈ selectedColumns m σ, Sum.elim z (fun i => (z i)⁻¹) j := by
    rw [selectedColumns, prod_image]
    · rfl
    · intro i _ j _ hij
      exact Sum.inr_injective (σ.injective hij)
  rw [hp, norm_div, norm_prod, norm_prod]
  have hn : (fun j : Fin m ⊕ Fin m => ‖Sum.elim z (fun i => (z i)⁻¹) j‖) =
      Sum.elim (fun i => ‖z i‖) (fun i => ‖z i‖⁻¹) := by
    funext j
    cases j <;> simp
  simp only [hn, norm_inv]
  apply nonleading_product_ratio_le m i₀ (fun i => ‖z i‖)
    (fun i => norm_pos_iff.mpr (hz i)) hz1 ρ hzρ
    (selectedColumns m σ) (selectedColumns_card m σ)
  · exact mt (selectedColumns_forall m σ (fun j => j.isRight)).mp hP
  · exact mt (selectedColumns_forall m σ
      (fun j => (Equiv.swap (Sum.inl i₀) (Sum.inr i₀) j).isRight)).mp hQ

end MF21Normalization
#print axioms MF21Normalization.nonleading_has_loss
#print axioms MF21Normalization.nonleading_product_ratio_le
