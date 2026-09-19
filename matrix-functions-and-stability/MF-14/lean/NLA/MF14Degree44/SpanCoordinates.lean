import NLA.MF14Degree44.Family
import NLA.MF14Degree44.CircuitSpanOperations
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin

/- General full-polynomial reconstruction from a nonsingular coefficient
matrix; no polynomial truncation or basis independence is assumed.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; Codex assistance. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
open scoped BigOperators
namespace NLA.MF14Degree44

def basisCoefficientMatrix {n : ℕ} (v : Fin n → Poly) (rows : Fin n → ℕ) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => (v j).coeff (rows i)

lemma span_representation {n : ℕ} (v : Fin n → Poly) (p : Poly)
    (hp : p ∈ Submodule.span ℂ (Set.range v)) :
    ∃ c : Fin n → ℂ, linearCombination c v = p := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hp
  exact ⟨c, by simpa only [linearCombination, smul_eq_C_mul] using hc⟩

lemma basis_coefficient_mulVec {n : ℕ} (v : Fin n → Poly) (rows : Fin n → ℕ)
    (c : Fin n → ℂ) :
    (basisCoefficientMatrix v rows).mulVec c =
      fun i => (linearCombination c v).coeff (rows i) := by
  funext i
  simp only [basisCoefficientMatrix, Matrix.mulVec, dotProduct, linearCombination,
    finsetSum_coeff, coeff_C_mul]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- This acts on the literal entire polynomial span, including any zero coefficients. -/
theorem coefficient_span_bijective {n : ℕ} (v : Fin n → Poly) (rows : Fin n → ℕ)
    (hdet : (basisCoefficientMatrix v rows).det ≠ 0) :
    Function.Bijective (fun p : Submodule.span ℂ (Set.range v) =>
      fun i => p.val.coeff (rows i)) := by
  classical
  let A := basisCoefficientMatrix v rows
  have hinj : Function.Injective A.mulVec := Matrix.mulVec_injective_of_det_ne_zero hdet
  have hsurj : Function.Surjective A.mulVec :=
    LinearMap.surjective_of_injective (f := A.mulVecLin) hinj
  constructor
  · intro p q hpq
    obtain ⟨c, hc⟩ := span_representation v p.val p.property
    obtain ⟨d, hd⟩ := span_representation v q.val q.property
    have heq : A.mulVec c = A.mulVec d := by
      rw [basis_coefficient_mulVec, basis_coefficient_mulVec, hc, hd]
      exact hpq
    have hcd := hinj heq
    apply Subtype.ext
    rw [← hc, ← hd, hcd]
  · intro y
    obtain ⟨c, hc⟩ := hsurj y
    have hp : linearCombination c v ∈ Submodule.span ℂ (Set.range v) :=
      linearCombination_mem _ c v (fun i => Submodule.subset_span (Set.mem_range_self i))
    refine ⟨⟨linearCombination c v, hp⟩, ?_⟩
    change (fun i => (linearCombination c v).coeff (rows i)) = y
    rw [← basis_coefficient_mulVec]
    exact hc

#print axioms span_representation
#assert_trust kernel span_representation
#print axioms basis_coefficient_mulVec
#assert_trust kernel basis_coefficient_mulVec
#print axioms coefficient_span_bijective
#assert_trust kernel coefficient_span_bijective
end NLA.MF14Degree44
