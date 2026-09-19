import NLA.MF14Degree44.FinalClosure

/- Complete solution of the unchanged original MF-14 target via degree44.
All 25 independently frozen contracts are imported and audited below.
The independent Challenge is never imported by the proof environment.
Mathematics: Marcus Webb, The University of Manchester; earlier degree42:
Matthew J. Colbrook, University of Cambridge. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology, with Codex assistance. -/
set_option leancert.trust "kernel"

#print axioms NLA.MF14Degree44.canonical_gate_padding
#assert_trust kernel NLA.MF14Degree44.canonical_gate_padding

#print axioms NLA.MF14Degree44.four_prefix_full_coefficients
#assert_trust kernel NLA.MF14Degree44.four_prefix_full_coefficients

#print axioms NLA.MF14Degree44.three_product_tuple
#assert_trust kernel NLA.MF14Degree44.three_product_tuple

#print axioms NLA.MF14Degree44.good_border_parameters_eventually
#assert_trust kernel NLA.MF14Degree44.good_border_parameters_eventually

#print axioms NLA.MF14Degree44.fourth_span_coordinates
#assert_trust kernel NLA.MF14Degree44.fourth_span_coordinates

#print axioms NLA.MF14Degree44.fourth_map_smooth
#assert_trust kernel NLA.MF14Degree44.fourth_map_smooth

#print axioms NLA.MF14Degree44.fourth_jacobian_identity
#assert_trust kernel NLA.MF14Degree44.fourth_jacobian_identity

#print axioms NLA.MF14Degree44.fourth_minor_identity
#assert_trust kernel NLA.MF14Degree44.fourth_minor_identity

#print axioms NLA.MF14Degree44.fourth_product_joint_closure
#assert_trust kernel NLA.MF14Degree44.fourth_product_joint_closure

#print axioms NLA.MF14Degree44.polynomial_density_of_strict_derivative
#assert_trust kernel NLA.MF14Degree44.polynomial_density_of_strict_derivative

#print axioms NLA.MF14Degree44.degeneration_identity
#assert_trust kernel NLA.MF14Degree44.degeneration_identity

#print axioms NLA.MF14Degree44.degeneration_at_zero
#assert_trust kernel NLA.MF14Degree44.degeneration_at_zero

#print axioms NLA.MF14Degree44.degeneration_in_span
#assert_trust kernel NLA.MF14Degree44.degeneration_in_span

#print axioms NLA.MF14Degree44.monic_border_joint_closure
#assert_trust kernel NLA.MF14Degree44.monic_border_joint_closure

#print axioms NLA.MF14Degree44.continuation_actual_output
#assert_trust kernel NLA.MF14Degree44.continuation_actual_output

#print axioms NLA.MF14Degree44.continuation_degree_bound
#assert_trust kernel NLA.MF14Degree44.continuation_degree_bound

#print axioms NLA.MF14Degree44.continuation_closure_transfer
#assert_trust kernel NLA.MF14Degree44.continuation_closure_transfer

#print axioms NLA.MF14Degree44.family_image_mem_closure
#assert_trust kernel NLA.MF14Degree44.family_image_mem_closure

#print axioms NLA.MF14Degree44.family_degree_and_full_vector
#assert_trust kernel NLA.MF14Degree44.family_degree_and_full_vector

#print axioms NLA.MF14Degree44.coefficient_map_smooth
#assert_trust kernel NLA.MF14Degree44.coefficient_map_smooth

#print axioms NLA.MF14Degree44.coefficient_jacobian_identity
#assert_trust kernel NLA.MF14Degree44.coefficient_jacobian_identity

#print axioms NLA.MF14Degree44.integer_jacobian_mod3_inverse
#assert_trust kernel NLA.MF14Degree44.integer_jacobian_mod3_inverse

#print axioms NLA.MF14Degree44.coefficient_derivative_bijective
#assert_trust kernel NLA.MF14Degree44.coefficient_derivative_bijective

#print axioms NLA.MF14Degree44.degree44_coverage
#assert_trust kernel NLA.MF14Degree44.degree44_coverage

#print axioms NLA.MF14Degree44.original_equality_false
#assert_trust kernel NLA.MF14Degree44.original_equality_false
