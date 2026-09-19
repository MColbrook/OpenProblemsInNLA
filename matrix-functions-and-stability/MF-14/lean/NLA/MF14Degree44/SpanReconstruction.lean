import NLA.MF14Degree44.SpanCoordinates
import NLA.MF14Degree44.PolynomialMaps

/- Full polynomial inverse-coordinate map; complex matrix coefficients are
fixed scalars, not numerical interval approximations. Formalization:
George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology; Codex assistance. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
open scoped BigOperators
namespace NLA.MF14Degree44

def spanReconstruct {n : ℕ} (v : Fin n → Poly) (rows : Fin n → ℕ) (y : Fin n → ℂ) : Poly :=
  linearCombination ((basisCoefficientMatrix v rows)⁻¹.mulVec y) v

lemma span_reconstruct_coordinates {n : ℕ} (v : Fin n → Poly) (rows : Fin n → ℕ)
    (hdet : (basisCoefficientMatrix v rows).det ≠ 0) (p : Poly)
    (hp : p ∈ Submodule.span ℂ (Set.range v)) :
    spanReconstruct v rows (fun i => p.coeff (rows i)) = p := by
  obtain ⟨c, hc⟩ := span_representation v p hp
  rw [← hc]
  unfold spanReconstruct
  rw [← basis_coefficient_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]

lemma matrix_mulVec_scalar_polynomial {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    ScalarPolynomial (fun y : Fin n → ℂ => A.mulVec y i) := by
  exact ScalarPolynomial.sum Finset.univ (fun j y => A i j * y j)
    (fun j => (ScalarPolynomial.const (A i j)).mul (ScalarPolynomial.variable j))

lemma span_reconstruct_coefficient_polynomial {n : ℕ} (v : Fin n → Poly) (rows : Fin n → ℕ) :
    CoefficientPolynomial (spanReconstruct v rows) := by
  exact CoefficientPolynomial.sum Finset.univ
    (fun i y => C (((basisCoefficientMatrix v rows)⁻¹).mulVec y i) * v i)
    (fun i => (CoefficientPolynomial.C
      (matrix_mulVec_scalar_polynomial ((basisCoefficientMatrix v rows)⁻¹) i)).mul
        (CoefficientPolynomial.const (v i)))

#print axioms span_reconstruct_coordinates
#assert_trust kernel span_reconstruct_coordinates
#print axioms span_reconstruct_coefficient_polynomial
#assert_trust kernel span_reconstruct_coefficient_polynomial
end NLA.MF14Degree44
