import NLA.MF14Degree44.DegreeBounds

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
open scoped BigOperators
namespace NLA.MF14Degree44

theorem family_degree_and_full_vector (theta : Parameters) :
    (familyPolynomial theta).natDegree ≤ 44 ∧
    fullFamilyVector theta = embed44 (coefficientMap theta) := by
  have h0 : (familyQuad theta 0).natDegree ≤ 5 := by
    change ((X : Poly) ^ 2).natDegree ≤ 5
    exact (natDegree_X_pow_le (R := ℂ) 2).trans (by decide)
  have h1 : (familyQuad theta 1).natDegree ≤ 5 := by
    change (Q (theta 0)).natDegree ≤ 5
    unfold Q
    exact natDegree_add_le_of_degree_le ((natDegree_X_pow_le 4).trans (by decide))
      ((natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le 3).trans (by decide)))
  have h2 : (familyQuad theta 2).natDegree ≤ 5 := by
    change (R (theta 1)).natDegree ≤ 5
    unfold R
    exact natDegree_add_le_of_degree_le (natDegree_X_pow_le 5)
      ((natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le 3).trans (by decide)))
  have h3 : (familyQuad theta 3).natDegree ≤ 12 := by
    change (monicBorderPolynomial (fun i : Fin 7 => theta (parameterIndex 2 (by decide) i))).natDegree ≤ 12
    exact monicBorderPolynomial_natDegree _
  have hd : (familyPolynomial theta).natDegree ≤ 44 :=
    continuation_natDegree_of_bounds theta (familyQuad theta) 12 5
      (by decide) (by decide) h0 h1 h2 h3
  refine ⟨hd, ?_⟩
  funext i
  change (familyPolynomial theta).coeff i.val =
    (if hi : i.val < 45 then (familyPolynomial theta).coeff (⟨i.val, hi⟩ : Fin 45).val else 0)
  split_ifs with hi
  · rfl
  · exact coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by omega))

#print axioms family_degree_and_full_vector
#assert_trust kernel family_degree_and_full_vector

end NLA.MF14Degree44
