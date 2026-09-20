import MF21.ActualBoundaryError
import MF21.BoundaryBlockForm

/-! Exact reconstruction of the actual determinant from the normalized finite remainder. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
open Set Finset
namespace MF21ActualBoundary
open MF21Bulk MF21Normalization

theorem remainder_sum_eq (m : ℕ) (hm : 0<m) (d : SlopeData m) (p : ℕ)
    (x : ℝ) (hx : x ∈ Ioc 0 Real.pi) :
    (∑ σ : Equiv.Perm (Fin m ⊕ Fin m),
      if ¬selects m (fun j => j.isRight) σ ∧
        ¬selects m (fun j =>
          (Equiv.swap (Sum.inl (⟨0,hm⟩ : Fin m)) (Sum.inr (⟨0,hm⟩ : Fin m)) j).isRight) σ then
        permutationCoefficient m (fun j => d.U j x) σ *
          permutationBase m (blockRootFamily m x) σ^p else 0) =
      slopeNormalizer m d.U x * rightProduct m x^p * normalizedRemainder m hm d p x := by
  classical
  rw [← sum_filter]
  rw [sum_subtype _ (p := fun σ =>
    ¬selects m (fun j => j.isRight) σ ∧
    ¬selects m (fun j => (Equiv.swap (Sum.inl (⟨0,hm⟩ : Fin m))
      (Sum.inr (⟨0,hm⟩ : Fin m)) j).isRight) σ) (by simp)]
  rw [normalizedRemainder, mul_sum]
  apply sum_congr rfl
  intro σ _
  rw [d.base_eq_actual σ.val x hx]
  unfold SlopeData.coefficient
  have hA := d.normalizer_ne_zero x ⟨hx.1.le,hx.2⟩
  have hB := rightProduct_ne_zero m hm x hx
  rw [div_pow]
  field_simp

/-- An arbitrary mask shares the exact endpoint normalization, so the two
leading Vandermonde coefficients scale by the same power as the determinant. -/
theorem masked_rescale (m : ℕ) (t : ℂ) (u z : Fin m ⊕ Fin m → ℂ)
    (hz : ∀ j, z j=1+t*u j) (P : Fin m ⊕ Fin m → Prop) [DecidablePred P] :
    (maskedBlock m z (fun _ => 1) P).det =
      t^(m*(m-1))*(maskedBlock m u (fun _ => 1) P).det := by
  unfold maskedBlock
  rw [show z=(fun j => 1+t*u j) from funext hz]
  exact blockPower_det_rescale_order m t u _

/-- Both leading coefficients inherit precisely the determinant's vanishing
order at the endpoint. -/
theorem leading_coefficient_rescale (m : ℕ) (t : ℂ) (u z : Fin m ⊕ Fin m → ℂ)
    (hz : ∀ j, z j=1+t*u j) :
    (Matrix.vandermonde (fun i => z (Sum.inl i))).det *
      (Matrix.vandermonde (fun i => z (Sum.inr i))).det =
      t^(m*(m-1))*((Matrix.vandermonde (fun i => u (Sum.inl i))).det *
        (Matrix.vandermonde (fun i => u (Sum.inr i))).det) := by
  simpa only [maskedBlock_right_det, prod_const_one, mul_one] using
    masked_rescale m t u z hz (fun j => j.isRight)

/-- Exact leading-pair plus remainder identity in the smoothly normalized slopes. -/
theorem determinant_two_leading_terms (m n : ℕ) (hm : 0<m) (d : SlopeData m)
    (x : ℝ) (hx : x ∈ Ioc 0 Real.pi) :
    determinant m n x = (halfSine x : ℂ)^(m*(m-1)) *
      ((maskedBlock m (fun j => d.U j x) (fun j => blockRootFamily m x j^(n+m))
          (fun j => j.isRight)).det +
        (maskedBlock m (fun j => d.U j x) (fun j => blockRootFamily m x j^(n+m))
          (fun j => (Equiv.swap (Sum.inl (⟨0,hm⟩ : Fin m))
            (Sum.inr (⟨0,hm⟩ : Fin m)) j).isRight)).det +
        slopeNormalizer m d.U x * rightProduct m x^(n+m) *
          normalizedRemainder m hm d (n+m) x) := by
  have he : blockRoots m x = blockRootFamily m x := by
    funext j
    cases j <;> simp [blockRootFamily]
  rw [determinant_rescale m n x (halfSine x) (fun j => d.U j x)
    (fun j => by rw [he]; exact d.factor j x hx), he]
  rw [blockPower_two_leading_terms m (n+m) (fun j => d.U j x) (blockRootFamily m x)
    (fun j => j.isRight) (fun j => (Equiv.swap
      (Sum.inl (⟨0,hm⟩ : Fin m)) (Sum.inr (⟨0,hm⟩ : Fin m)) j).isRight)
    (dominant_selections_disjoint m ⟨0,hm⟩), remainder_sum_eq m hm d (n+m) x hx]

end MF21ActualBoundary
#print axioms MF21ActualBoundary.determinant_two_leading_terms
#print axioms MF21ActualBoundary.leading_coefficient_rescale
