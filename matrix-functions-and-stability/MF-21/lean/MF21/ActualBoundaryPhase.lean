import MF21.ActualBoundaryExpansion
import MF21.BoundaryReality
import MF21.BulkLeadingPhase
import MF21.RealBoundaryError

/-! Exact real sine equation for the actual Toeplitz boundary determinant. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
open Set Finset
namespace MF21ActualBoundary
open MF21Bulk MF21Normalization

theorem masked_rescale_weighted (m : ℕ) (t : ℂ) (u z w : Fin m ⊕ Fin m → ℂ)
    (hz : ∀ j, z j = 1+t*u j) (P : Fin m ⊕ Fin m → Prop) [DecidablePred P] :
    (maskedBlock m z w P).det =
      t^(m*(m-1))*(maskedBlock m u w P).det := by
  unfold maskedBlock
  rw [show z=(fun j => 1+t*u j) from funext hz]
  exact blockPower_det_rescale_order m t u _

theorem root_masked_right (m n : ℕ) (hm : 0<m) (x : ℝ) :
    (maskedBlock m (blockRootFamily m x) (fun j => blockRootFamily m x j^(n+m))
      (fun j => j.isRight)).det = rootLeadingAmplitude m n x := by
  rw [maskedBlock_right_power]
  change (Matrix.vandermonde (baseRoot m x)).det *
    (Matrix.vandermonde (fun j => (baseRoot m x j)⁻¹)).det *
    (∏ j : Fin m, (baseRoot m x j)⁻¹)^(n+m) = _
  rw [root_coefficient_eq_pair m hm x, root_inverse_product_eq m hm x]
  rfl

theorem swapped_left_cons (k : ℕ) (x : ℝ) :
    (fun i : Fin (k+1) => blockRootFamily (k+1) x
      (Equiv.swap (Sum.inl (0 : Fin (k+1))) (Sum.inr (0 : Fin (k+1))) (Sum.inl i))) =
      Fin.cons (unitRoot x)⁻¹ (stableTail (k+1) x) := by
  classical
  funext i
  induction i using Fin.cases with
  | zero => simp [blockRootFamily, baseRoot]
  | succ i =>
    simp only [Equiv.swap_apply_of_ne_of_ne (by simp : (Sum.inl i.succ : Fin (k+1) ⊕ Fin (k+1)) ≠ Sum.inl 0)
      (by simp : (Sum.inl i.succ : Fin (k+1) ⊕ Fin (k+1)) ≠ Sum.inr 0),
      blockRootFamily, Sum.elim_inl, baseRoot_cons, Fin.cons_succ]

theorem swapped_right_cons (k : ℕ) (x : ℝ) :
    (fun i : Fin (k+1) => blockRootFamily (k+1) x
      (Equiv.swap (Sum.inl (0 : Fin (k+1))) (Sum.inr (0 : Fin (k+1))) (Sum.inr i))) =
      Fin.cons (unitRoot x) (fun j => (stableTail (k+1) x j)⁻¹) := by
  classical
  funext i
  induction i using Fin.cases with
  | zero => simp [blockRootFamily, baseRoot]
  | succ i =>
    simp only [Equiv.swap_apply_of_ne_of_ne (by simp : (Sum.inr i.succ : Fin (k+1) ⊕ Fin (k+1)) ≠ Sum.inl 0)
      (by simp : (Sum.inr i.succ : Fin (k+1) ⊕ Fin (k+1)) ≠ Sum.inr 0),
      blockRootFamily, Sum.elim_inr, baseRoot_cons, Fin.cons_succ]

theorem root_masked_swap (m n : ℕ) (hm : 0<m) (x : ℝ) :
    (maskedBlock m (blockRootFamily m x) (fun j => blockRootFamily m x j^(n+m))
      (fun j => (Equiv.swap (Sum.inl (⟨0,hm⟩ : Fin m))
        (Sum.inr (⟨0,hm⟩ : Fin m)) j).isRight)).det =
      -(pairCoefficient (m-1) (unitRoot x)⁻¹ (stableTail m x) *
        (unitRoot x * tailInverseProduct m x)^(n+m)) := by
  classical
  rw [maskedBlock_swap_det m _ _ (by simp), Finset.prod_pow]
  cases m with
  | zero => omega
  | succ k =>
    change -( (Matrix.vandermonde (fun i => blockRootFamily (k+1) x
      (Equiv.swap (Sum.inl (0 : Fin (k+1))) (Sum.inr (0 : Fin (k+1))) (Sum.inl i)))).det *
      (Matrix.vandermonde (fun i => blockRootFamily (k+1) x
      (Equiv.swap (Sum.inl (0 : Fin (k+1))) (Sum.inr (0 : Fin (k+1))) (Sum.inr i)))).det *
      (∏ i : Fin (k+1), blockRootFamily (k+1) x
      (Equiv.swap (Sum.inl (0 : Fin (k+1))) (Sum.inr (0 : Fin (k+1))) (Sum.inr i)))^(n+(k+1))) = _
    rw [swapped_left_cons, swapped_right_cons]
    have hp : (∏ i : Fin (k+1), Fin.cons (unitRoot x)
        (fun j => (stableTail (k+1) x j)⁻¹) i) = unitRoot x * tailInverseProduct (k+1) x := by
      rw [Fin.prod_univ_succ]
      rfl
    rw [hp]
    simp only [pairCoefficient, inv_inv]

theorem rootLeadingAmplitude_rescale (m n : ℕ) (hm : 0<m) (d : SlopeData m)
    (x : ℝ) (hx : x ∈ Ioc 0 Real.pi) :
    rootLeadingAmplitude m n x = (halfSine x : ℂ)^(m*(m-1)) *
      (slopeNormalizer m d.U x * rightProduct m x^(n+m)) := by
  rw [← root_masked_right m n hm x,
    masked_rescale_weighted m (halfSine x) (fun j => d.U j x) (blockRootFamily m x)
      _ (fun j => d.factor j x hx), maskedBlock_right_power]
  rfl

theorem rootLeadingAmplitude_ne_zero (m n : ℕ) (hm : 0<m) (d : SlopeData m)
    (x : ℝ) (hx : x ∈ Ioc 0 Real.pi) : rootLeadingAmplitude m n x ≠ 0 := by
  rw [rootLeadingAmplitude_rescale m n hm d x hx]
  exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (ne_of_gt (halfSine_pos x hx))))
    (mul_ne_zero (d.normalizer_ne_zero x ⟨hx.1.le,hx.2⟩)
      (pow_ne_zero _ (rightProduct_ne_zero m hm x hx)))


theorem determinant_leading_remainder (m n : ℕ) (hm : 0<m) (d : SlopeData m)
    (x : ℝ) (hx : x ∈ Ioc 0 Real.pi) :
    determinant m n x = rootLeadingAmplitude m n x -
      pairCoefficient (m-1) (unitRoot x)⁻¹ (stableTail m x) *
        (unitRoot x * tailInverseProduct m x)^(n+m) +
      rootLeadingAmplitude m n x * normalizedRemainder m hm d (n+m) x := by
  have hright := masked_rescale_weighted m (halfSine x) (fun j => d.U j x)
    (blockRootFamily m x) (fun j => blockRootFamily m x j^(n+m))
    (fun j => d.factor j x hx) (fun j => j.isRight)
  have hswap := masked_rescale_weighted m (halfSine x) (fun j => d.U j x)
    (blockRootFamily m x) (fun j => blockRootFamily m x j^(n+m))
    (fun j => d.factor j x hx) (fun j => (Equiv.swap
      (Sum.inl (⟨0,hm⟩ : Fin m)) (Sum.inr (⟨0,hm⟩ : Fin m)) j).isRight)
  rw [root_masked_right m n hm x] at hright
  rw [root_masked_swap m n hm x] at hswap
  rw [determinant_two_leading_terms m n hm d x hx]
  linear_combination hright.symm + hswap.symm +
    (normalizedRemainder m hm d (n+m) x) * (rootLeadingAmplitude_rescale m n hm d x hx).symm

def sineNormalizer (m n : ℕ) (x : ℝ) : ℂ :=
  -2 * Complex.I * rootLeadingAmplitude m n x * unitRoot (secularPhase m n x)

theorem sineNormalizer_nonzero (m n : ℕ) (hm : 0<m) (d : SlopeData m)
    (x : ℝ) (hx : x ∈ Ioc 0 Real.pi) : sineNormalizer m n x ≠ 0 :=
  sineNormalizer_ne_zero _ _ (rootLeadingAmplitude_ne_zero m n hm d x hx)

theorem determinant_sine_remainder (m n : ℕ) (hm : 0<m) (d : SlopeData m)
    (x : ℝ) (hx : x ∈ Ioc 0 Real.pi) :
    determinant m n x = sineNormalizer m n x *
      ((Real.sin (secularPhase m n x) : ℂ) +
        (Complex.I/2)*unitRoot (-secularPhase m n x)*normalizedRemainder m hm d (n+m) x) := by
  rw [determinant_leading_remainder m n hm d x hx,
    actual_leading_pair_sine m n hm x (spectralBase_pos_of_mem x hx)]
  have he : unitRoot (secularPhase m n x) * unitRoot (-secularPhase m n x) = 1 := by
    rw [← unitRoot_add, add_neg_cancel]
    simp [unitRoot]
  unfold sineNormalizer
  linear_combination -rootLeadingAmplitude m n x * normalizedRemainder m hm d (n+m) x * he +
    (rootLeadingAmplitude m n x * unitRoot (secularPhase m n x) *
      normalizedRemainder m hm d (n+m) x * unitRoot (-secularPhase m n x)) * Complex.I_sq

theorem quantizationPhase_eq_secular (m n : ℕ) (eta : ℝ → ℝ) (x : ℝ)
    (he : eta x = x+2*psi m x) : quantizationPhase eta n x = secularPhase m n x := by
  unfold quantizationPhase secularPhase
  rw [he]
  ring

theorem determinant_complexError (m n : ℕ) (hm : 0<m) (d : SlopeData m)
    (eta : ℝ → ℝ) (x : ℝ) (hx : x ∈ Ioc 0 Real.pi)
    (he : eta x = x+2*psi m x) :
    determinant m n x = sineNormalizer m n x *
      ((Real.sin (quantizationPhase eta n x) : ℂ) + complexError m hm d eta n x) := by
  unfold complexError phaseRotate
  rw [quantizationPhase_eq_secular m n eta x he]
  exact determinant_sine_remainder m n hm d x hx

theorem complexError_im_zero (m n : ℕ) (hm : 0<m) (d : SlopeData m)
    (eta : ℝ → ℝ) (x : ℝ) (hx : x ∈ Ioc 0 Real.pi)
    (he : eta x = x+2*psi m x) : (complexError m hm d eta n x).im = 0 := by
  have hreal := normalized_boundary_real (determinant m n x) (rootLeadingAmplitude m n x)
    (secularPhase m n x) (determinant_conj m n hm x hx)
    (rootLeadingAmplitude_conj m n hm x (spectralBase_pos_of_mem x hx))
  change (determinant m n x / sineNormalizer m n x).im = 0 at hreal
  rw [determinant_complexError m n hm d eta x hx he,
    mul_div_cancel_left₀ _ (sineNormalizer_nonzero m n hm d x hx)] at hreal
  simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using hreal

theorem determinant_realError (m n : ℕ) (hm : 0<m) (d : SlopeData m)
    (eta : ℝ → ℝ) (x : ℝ) (hx : x ∈ Ioc 0 Real.pi)
    (he : eta x = x+2*psi m x) :
    determinant m n x = sineNormalizer m n x *
      ((Real.sin (quantizationPhase eta n x) + realError m hm d eta n x : ℝ) : ℂ) := by
  rw [determinant_complexError m n hm d eta x hx he, Complex.ofReal_add]
  congr 2
  apply Complex.ext
  · rfl
  · simp [complexError_im_zero m n hm d eta x hx he]

theorem determinant_zero_iff_sine (m n : ℕ) (hm : 0<m) (d : SlopeData m)
    (eta : ℝ → ℝ) (x : ℝ) (hx : x ∈ Ioc 0 Real.pi)
    (he : eta x = x+2*psi m x) : determinant m n x = 0 ↔
      Real.sin (quantizationPhase eta n x) + realError m hm d eta n x = 0 := by
  rw [determinant_realError m n hm d eta x hx he,
    mul_eq_zero, or_iff_right (sineNormalizer_nonzero m n hm d x hx), Complex.ofReal_eq_zero]


theorem realError_pi (m n : ℕ) (hm : 0<m) (d : SlopeData m)
    (eta : ℝ → ℝ) (he : eta Real.pi = Real.pi) :
    realError m hm d eta n Real.pi = 0 := by
  have hpi : Real.pi ∈ Ioc 0 Real.pi := ⟨Real.pi_pos, le_rfl⟩
  have hactual : eta Real.pi = Real.pi + 2*psi m Real.pi := by
    rw [he, psi_pi m hm]
    ring
  have hz := (determinant_zero_iff_sine m n hm d eta Real.pi hpi hactual).mp
    (determinant_pi m n hm)
  have hf : quantizationPhase eta n Real.pi = (n+1 : ℕ)*Real.pi := by
    unfold quantizationPhase
    rw [he]
    push_cast
    ring
  rw [hf, Real.sin_nat_mul_pi, zero_add] at hz
  exact hz

end MF21ActualBoundary
#print axioms MF21ActualBoundary.determinant_realError
#print axioms MF21ActualBoundary.determinant_zero_iff_sine
#print axioms MF21ActualBoundary.complexError_im_zero
