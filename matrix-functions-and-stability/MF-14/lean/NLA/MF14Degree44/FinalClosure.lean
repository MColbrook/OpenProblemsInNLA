import NLA.MF14Degree44.FourthJointClosure
import NLA.MF14Degree44.BorderLimit
import NLA.MF14Degree44.ContinuationClosure
import NLA.MF14Degree44.CoverageBridge
import NLA.MF14Degree44.FamilySmooth
import NLA.MF14Degree44.JacobianIdentity

/- Complete degree-44 coverage in the original full coefficient space.
Mathematics: Marcus Webb, The University of Manchester. Earlier degree-42
result: Matthew J. Colbrook, University of Cambridge. Formalization: George
Stepaniants, Department of Computing and Mathematical Sciences, California
Institute of Technology; Codex assistance. No degree-47 assertion is made. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
namespace NLA.MF14Degree44

lemma quad_reconstruction_of_degree (v : Quad)
    (hv : ∀ i : Fin 4, (v i).natDegree ≤ 16) : decodeQuad (quadVector v) = v := by
  funext i
  change (∑ k : Fin 17, C ((v i).coeff k.val) * X ^ k.val) = v i
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => C ((v i).coeff k) * X ^ k) 17]
  exact ((v i).as_sum_range_C_mul_X_pow' (lt_of_le_of_lt (hv i) (by decide))).symm

lemma border_quad_natDegree (alpha beta : ℂ) (xi : Fin 7 → ℂ) (i : Fin 4) :
    (borderQuad alpha beta xi i).natDegree ≤ 16 := by
  fin_cases i
  · change ((X : Poly) ^ 2).natDegree ≤ 16
    exact (natDegree_X_pow_le (R := ℂ) 2).trans (by decide)
  · change (Q alpha).natDegree ≤ 16
    unfold Q
    exact natDegree_add_le_of_degree_le ((natDegree_X_pow_le 4).trans (by decide))
      ((natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le 3).trans (by decide)))
  · change (R beta).natDegree ≤ 16
    unfold R
    exact natDegree_add_le_of_degree_le ((natDegree_X_pow_le 5).trans (by decide))
      ((natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le 3).trans (by decide)))
  · change (monicBorderPolynomial xi).natDegree ≤ 16
    exact (monicBorderPolynomial_natDegree xi).trans (by decide)

theorem monic_border_joint_closure (alpha beta : ℂ) (xi : Fin 7 → ℂ) :
    quadVector (borderQuad alpha beta xi) ∈ jointFourClosure := by
  exact monic_border_joint_closure_of_fourth fourth_product_joint_closure alpha beta xi

theorem family_image_mem_closure (theta : Parameters) :
    fullFamilyVector theta ∈ NLA.MF14.sevenProductClosure := by
  have hz : quadVector (familyQuad theta) ∈ jointFourClosure :=
    monic_border_joint_closure (theta 0) (theta 1)
      (fun i : Fin 7 => theta (parameterIndex 2 (by decide) i))
  have hrec : decodeQuad (quadVector (familyQuad theta)) = familyQuad theta :=
    quad_reconstruction_of_degree _ (border_quad_natDegree _ _ _)
  have h := continuation_closure_transfer theta _ hz
  change NLA.MF14.coefficientVector
    (continuationPolynomial theta (decodeQuad (quadVector (familyQuad theta)))) ∈
      NLA.MF14.sevenProductClosure at h
  rw [hrec] at h
  exact h

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem degree44_coverage : NLA.MF14.CoversDegree 44 := by
  apply degree44_coverage_of_density_and_image _ family_image_mem_closure
  apply polynomial_density_of_smooth_jacobian 45 coefficientMap basePoint coefficient_map_smooth
  rw [coefficient_jacobian_identity]
  exact complex_integer_jacobian_det_ne_zero

theorem original_equality_false : ¬ IsGreatest NLA.MF14.coveredDegrees 42 := by
  exact original_equality_false_of_coverage44 degree44_coverage

#print axioms quad_reconstruction_of_degree
#assert_trust kernel quad_reconstruction_of_degree
#print axioms border_quad_natDegree
#assert_trust kernel border_quad_natDegree
#print axioms monic_border_joint_closure
#assert_trust kernel monic_border_joint_closure
#print axioms family_image_mem_closure
#assert_trust kernel family_image_mem_closure
#print axioms degree44_coverage
#assert_trust kernel degree44_coverage
#print axioms original_equality_false
#assert_trust kernel original_equality_false
end NLA.MF14Degree44
