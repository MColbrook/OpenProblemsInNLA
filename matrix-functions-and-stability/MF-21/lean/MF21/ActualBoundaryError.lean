import MF21.ActualBoundaryDecay
import MF21.ExponentialSums

/-! Smooth coefficients and uniform bounds for the actual determinant remainder. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Topology ContDiff
open Set
namespace MF21ActualBoundary
open MF21Bulk MF21Normalization

structure SlopeData (m : ℕ) where
  U : (Fin m ⊕ Fin m) → ℝ → ℂ
  smooth : ∀ j x, x ∈ Icc 0 Real.pi → ContDiffAt ℝ ∞ (U j) x
  factor : ∀ j x, x ∈ Ioc 0 Real.pi →
    blockRootFamily m x j = 1+(halfSine x : ℂ)*U j x
  normalizer_ne_zero : ∀ x ∈ Icc 0 Real.pi, slopeNormalizer m U x ≠ 0
  normalizer_smooth : ∀ x ∈ Icc 0 Real.pi, ContDiffAt ℝ ∞ (slopeNormalizer m U) x

theorem slopeData_exists (m : ℕ) (hm : 0<m) : Nonempty (SlopeData m) := by
  obtain ⟨U, _, hs, hf, hn, hc⟩ := block_slopes_exist m hm
  exact ⟨⟨U,hs,hf,hn,hc⟩⟩

namespace SlopeData
variable {m : ℕ} (d : SlopeData m)

def extendedRoot (j : Fin m ⊕ Fin m) (x : ℝ) : ℂ :=
  1+(halfSine x : ℂ)*d.U j x

theorem extendedRoot_smooth (j : Fin m ⊕ Fin m) (x : ℝ) (hx : x ∈ Icc 0 Real.pi) :
    ContDiffAt ℝ ∞ (d.extendedRoot j) x := by
  exact contDiffAt_const.add ((Complex.ofRealCLM.contDiff.contDiffAt.comp x
    halfSine_contDiff.contDiffAt).mul (d.smooth j x hx))

theorem extendedRoot_ne_zero (hm : 0<m) (j : Fin m ⊕ Fin m)
    (x : ℝ) (hx : x ∈ Icc 0 Real.pi) : d.extendedRoot j x ≠ 0 := by
  by_cases he : x=0
  · simp [extendedRoot, he, halfSine]
  · have hx' : x ∈ Ioc 0 Real.pi := ⟨lt_of_le_of_ne hx.1 (Ne.symm he), hx.2⟩
    rw [extendedRoot, ← d.factor j x hx']
    cases j with
    | inl j => exact (baseRoot_spec_of_pos m hm x (spectralBase_pos_of_mem x hx') j).1
    | inr j => exact inv_ne_zero (baseRoot_spec_of_pos m hm x (spectralBase_pos_of_mem x hx') j).1

def coefficient (σ : Equiv.Perm (Fin m ⊕ Fin m)) (x : ℝ) : ℂ :=
  permutationCoefficient m (fun j => d.U j x) σ / slopeNormalizer m d.U x

def base (σ : Equiv.Perm (Fin m ⊕ Fin m)) (x : ℝ) : ℂ :=
  permutationBase m (fun j => d.extendedRoot j x) σ /
    (∏ i : Fin m, d.extendedRoot (Sum.inr i) x)

theorem coefficient_smooth (σ : Equiv.Perm (Fin m ⊕ Fin m))
    (x : ℝ) (hx : x ∈ Icc 0 Real.pi) : ContDiffAt ℝ ∞ (d.coefficient σ) x := by
  unfold coefficient permutationCoefficient
  simp only [Units.smul_def, zsmul_eq_mul]
  simp only [div_eq_mul_inv]
  apply ContDiffAt.mul _ ((d.normalizer_smooth x hx).inv (d.normalizer_ne_zero x hx))
  apply contDiffAt_const.mul
  apply ContDiffAt.mul
  all_goals
    apply contDiffAt_prod
    intro i _
    exact (d.smooth _ x hx).pow i.val

theorem base_smooth (hm : 0<m) (σ : Equiv.Perm (Fin m ⊕ Fin m))
    (x : ℝ) (hx : x ∈ Icc 0 Real.pi) : ContDiffAt ℝ ∞ (d.base σ) x := by
  unfold base permutationBase
  simp only [div_eq_mul_inv]
  apply ContDiffAt.mul
  · exact contDiffAt_prod (fun i _ => d.extendedRoot_smooth _ x hx)
  · apply ContDiffAt.inv
    · exact contDiffAt_prod (fun i _ => d.extendedRoot_smooth _ x hx)
    · exact Finset.prod_ne_zero_iff.mpr (fun i _ => d.extendedRoot_ne_zero hm _ x hx)

theorem base_ne_zero (hm : 0<m) (σ : Equiv.Perm (Fin m ⊕ Fin m))
    (x : ℝ) (hx : x ∈ Icc 0 Real.pi) : d.base σ x ≠ 0 := by
  apply div_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => d.extendedRoot_ne_zero hm _ x hx)
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => d.extendedRoot_ne_zero hm _ x hx)

theorem base_eq_actual (σ : Equiv.Perm (Fin m ⊕ Fin m))
    (x : ℝ) (hx : x ∈ Ioc 0 Real.pi) :
    d.base σ x = permutationBase m (blockRootFamily m x) σ / rightProduct m x := by
  have he : (fun j => d.extendedRoot j x) = blockRootFamily m x :=
    funext (fun j => (d.factor j x hx).symm)
  unfold base
  rw [he]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact congrFun he (Sum.inr i)

end SlopeData

abbrev Nonleading (m : ℕ) (hm : 0<m) :=
  {σ : Equiv.Perm (Fin m ⊕ Fin m) //
    ¬selects m (fun j => j.isRight) σ ∧
    ¬selects m (fun j =>
      (Equiv.swap (Sum.inl (⟨0,hm⟩ : Fin m)) (Sum.inr (⟨0,hm⟩ : Fin m)) j).isRight) σ}

def normalizedRemainder (m : ℕ) (hm : 0<m) (d : SlopeData m) (p : ℕ) (x : ℝ) : ℂ := by
  classical
  exact ∑ σ : Nonleading m hm, d.coefficient σ.val x * d.base σ.val x^p

/-- The coefficient smoothness, nonvanishing, and exponential decay have all
been proved for the actual root family. -/
theorem normalizedRemainder_bounds (m : ℕ) (hm : 0<m) (d : SlopeData m) :
    ∃ c : ℝ, 0<c ∧ ∃ C : ℝ, 0<C ∧ ∀ p : ℕ, ∀ x ∈ Ioc 0 Real.pi,
      ‖normalizedRemainder m hm d p x‖ ≤ C*Real.exp (-c*p*x) ∧
      ‖deriv (normalizedRemainder m hm d p) x‖ ≤ C*(p+1)*Real.exp (-c*p*x) := by
  classical
  obtain ⟨c,hc,hdecay⟩ := nonleading_actual_exp_bound m hm
  obtain ⟨C,hC,hbound⟩ := MF21ExpSums.uniform_exponential_sum_bounds
    (fun σ : Nonleading m hm => d.coefficient σ.val)
    (fun σ : Nonleading m hm => d.base σ.val) Real.pi c
    (fun σ x hx => d.coefficient_smooth σ.val x hx)
    (fun σ x hx => d.base_smooth hm σ.val x hx)
    (fun σ x hx => d.base_ne_zero hm σ.val x hx)
    (fun σ x hx => by rw [d.base_eq_actual σ.val x hx]; exact hdecay x hx σ.val σ.prop.1 σ.prop.2)
  exact ⟨c,hc,C,hC,hbound⟩

end MF21ActualBoundary
#print axioms MF21ActualBoundary.normalizedRemainder_bounds
#print axioms MF21ActualBoundary.slopeData_exists
