import MF21.BoundaryLeadingTerms
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-! The exact two-leading-term decomposition with a finite remainder. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace MF21Normalization

def permutationCoefficient (m : ℕ) (u : Fin m ⊕ Fin m → ℂ)
    (σ : Equiv.Perm (Fin m ⊕ Fin m)) : ℂ :=
  Equiv.Perm.sign σ • ((∏ i : Fin m, u (σ (Sum.inl i))^i.val) *
    (∏ i : Fin m, u (σ (Sum.inr i))^i.val))

def permutationBase (m : ℕ) (z : Fin m ⊕ Fin m → ℂ)
    (σ : Equiv.Perm (Fin m ⊕ Fin m)) : ℂ :=
  ∏ i : Fin m, z (σ (Sum.inr i))

abbrev selects (m : ℕ) (P : Fin m ⊕ Fin m → Prop)
    (σ : Equiv.Perm (Fin m ⊕ Fin m)) : Prop :=
  ∀ i : Fin m, P (σ (Sum.inr i))

theorem blockPower_expansion (m p : ℕ) (u z : Fin m ⊕ Fin m → ℂ) :
    (blockPower m u (fun j => z j^p)).det =
      ∑ σ : Equiv.Perm (Fin m ⊕ Fin m),
        permutationCoefficient m u σ * (permutationBase m z σ)^p := by
  rw [blockPower_det_expansion]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [permutationCoefficient, permutationBase, smul_mul_assoc]

theorem maskedBlock_expansion (m p : ℕ) (u z : Fin m ⊕ Fin m → ℂ)
    (P : Fin m ⊕ Fin m → Prop) [DecidablePred P] :
    (maskedBlock m u (fun j => z j^p) P).det =
      ∑ σ : Equiv.Perm (Fin m ⊕ Fin m), if selects m P σ then
        permutationCoefficient m u σ * (permutationBase m z σ)^p else 0 := by
  classical
  rw [← Matrix.det_transpose, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Matrix.transpose_apply, Fintype.prod_sum_type, maskedBlock,
    blockPower, Sum.elim_inl, Sum.elim_inr, Finset.prod_mul_distrib,
    Fintype.prod_ite_zero, Finset.prod_pow, selects]
  split_ifs
  · simp only [permutationCoefficient, permutationBase, Units.smul_def, zsmul_eq_mul]
    ring
  · simp

/-- Removing two disjoint selected classes leaves exactly the remaining
permutation terms; no estimate or asymptotic assumption enters this identity. -/
theorem blockPower_two_leading_terms (m p : ℕ) (u z : Fin m ⊕ Fin m → ℂ)
    (P Q : Fin m ⊕ Fin m → Prop) [DecidablePred P] [DecidablePred Q]
    (hd : ∀ σ, ¬(selects m P σ ∧ selects m Q σ)) :
    (blockPower m u (fun j => z j^p)).det =
      (maskedBlock m u (fun j => z j^p) P).det +
      (maskedBlock m u (fun j => z j^p) Q).det +
      ∑ σ : Equiv.Perm (Fin m ⊕ Fin m),
        if ¬selects m P σ ∧ ¬selects m Q σ then
          permutationCoefficient m u σ * (permutationBase m z σ)^p else 0 := by
  classical
  rw [blockPower_expansion, maskedBlock_expansion, maskedBlock_expansion,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases hP : selects m P σ <;> by_cases hQ : selects m Q σ
  · exact (hd σ ⟨hP, hQ⟩).elim
  all_goals simp [hP, hQ]


/-- A permutation cannot send all lower rows into both dominant column sets. -/
theorem dominant_selections_disjoint (m : ℕ) (i₀ : Fin m)
    (σ : Equiv.Perm (Fin m ⊕ Fin m)) :
    ¬(selects m (fun j => j.isRight) σ ∧
      selects m (fun j => (Equiv.swap (Sum.inl i₀) (Sum.inr i₀) j).isRight) σ) := by
  intro ⟨hP, hQ⟩
  let f : Fin m → Fin m := fun i => (σ (Sum.inr i)).getRight (hP i)
  have hf : Function.Injective f := by
    intro i j hij
    apply Sum.inr_injective
    apply σ.injective
    have hh := congrArg (Sum.inr : Fin m → Fin m ⊕ Fin m) hij
    simpa only [f, Sum.inr_getRight] using hh
  obtain ⟨i, hi⟩ := Finite.surjective_of_injective hf i₀
  have he : σ (Sum.inr i) = Sum.inr i₀ := by
    exact (Sum.getRight_eq_iff (hP i)).mp hi
  have h := hQ i
  simpa [he] using h

end MF21Normalization
#print axioms MF21Normalization.maskedBlock_expansion
#print axioms MF21Normalization.blockPower_two_leading_terms
