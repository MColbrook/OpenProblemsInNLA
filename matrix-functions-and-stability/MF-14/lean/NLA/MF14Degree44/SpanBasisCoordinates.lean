import NLA.MF14Degree44.BasisDegreeData
import NLA.MF14Degree44.SpanCoordinates
import NLA.MF14Degree44.FourthSpanMembership
import Mathlib.LinearAlgebra.Matrix.Block

/- Exact triangular coordinate reconstruction for Marcus Webb's full span.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; Codex assistance. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
open scoped BigOperators
namespace NLA.MF14Degree44

lemma fourth_rows_strictMono : StrictMono (fun i : Fin 12 => (fourthRows i).val) := by
  decide +kernel

lemma product_basis_matrix_upper (alpha eta gamma s : ℂ) :
    (basisCoefficientMatrix (productSpanBasis alpha eta gamma s)
      (fun i => (fourthRows i).val)).IsUpperTriangular := by
  intro i j hji
  exact coeff_eq_zero_of_natDegree_lt
    ((product_span_basis_degree_le alpha eta gamma s j).trans_lt (fourth_rows_strictMono hji))

lemma product_basis_matrix_det (alpha eta gamma s : ℂ) :
    (basisCoefficientMatrix (productSpanBasis alpha eta gamma s)
      (fun i => (fourthRows i).val)).det = s ^ 10 := by
  rw [Matrix.det_of_isUpperTriangular (product_basis_matrix_upper alpha eta gamma s)]
  simp only [basisCoefficientMatrix, product_span_basis_diagonal]
  norm_num [Fin.prod_univ_succ]
  <;> ring

/-- D44-03a: exact full-span coordinates; no degree projection of actual outputs. -/
theorem fourth_span_coordinates (alpha eta gamma s lam : ℂ) (hs : s ≠ 0) :
    (∀ t : Fin 12 → ℂ,
      fourthPolynomial alpha eta gamma s lam t ∈ productSpan alpha eta gamma s) ∧
    Function.Bijective (fun p : productSpan alpha eta gamma s => fourthCoordinates p.1) := by
  refine ⟨fourth_polynomial_mem_product_span alpha eta gamma s lam, ?_⟩
  apply coefficient_span_bijective (productSpanBasis alpha eta gamma s)
    (fun i => (fourthRows i).val)
  rw [product_basis_matrix_det]
  exact pow_ne_zero 10 hs

#print axioms fourth_rows_strictMono
#assert_trust kernel fourth_rows_strictMono
#print axioms product_basis_matrix_upper
#assert_trust kernel product_basis_matrix_upper
#print axioms product_basis_matrix_det
#assert_trust kernel product_basis_matrix_det
#print axioms fourth_span_coordinates
#assert_trust kernel fourth_span_coordinates
end NLA.MF14Degree44
