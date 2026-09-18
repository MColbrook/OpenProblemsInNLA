/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.
Prior mathematical authorship and unchanged reused-code authorship are retained
in the component headers and REUSE-MI24-FURUTA.json. This aggregate requests
all 20 frozen axiom and kernel-trust checks. Its existence is not execution
evidence; actual serial local runs and final Linux gates are recorded separately.
-/
import NLA.MI28.DeterminantComparison

set_option autoImplicit false
set_option leancert.trust "kernel"

#print axioms NLA.MI28.half_exponent_interval
#assert_trust kernel NLA.MI28.half_exponent_interval
#print axioms NLA.MI28.product_modulus_square
#assert_trust kernel NLA.MI28.product_modulus_square
#print axioms NLA.MI28.swapped_modulus
#assert_trust kernel NLA.MI28.swapped_modulus
#print axioms NLA.MI28.normalized_posdef
#assert_trust kernel NLA.MI28.normalized_posdef
#print axioms NLA.MI28.furuta_boundary
#assert_trust kernel NLA.MI28.furuta_boundary
#print axioms NLA.MI28.furuta_admissible
#assert_trust kernel NLA.MI28.furuta_admissible
#print axioms NLA.MI28.lower_power_implication
#assert_trust kernel NLA.MI28.lower_power_implication
#print axioms NLA.MI28.higher_power_implication
#assert_trust kernel NLA.MI28.higher_power_implication
#print axioms NLA.MI28.swap_implication
#assert_trust kernel NLA.MI28.swap_implication
#print axioms NLA.MI28.small_base_implication
#assert_trust kernel NLA.MI28.small_base_implication
#print axioms NLA.MI28.small_base_norm
#assert_trust kernel NLA.MI28.small_base_norm
#print axioms NLA.MI28.large_base_norm
#assert_trust kernel NLA.MI28.large_base_norm
#print axioms NLA.MI28.normalized_homogeneity
#assert_trust kernel NLA.MI28.normalized_homogeneity
#print axioms NLA.MI28.normalized_norm_continuous
#assert_trust kernel NLA.MI28.normalized_norm_continuous
#print axioms NLA.MI28.full_log_majorization
#assert_trust kernel NLA.MI28.full_log_majorization
#print axioms NLA.MI28.log_one_add_tangent
#assert_trust kernel NLA.MI28.log_one_add_tangent
#print axioms NLA.MI28.product_one_add_le
#assert_trust kernel NLA.MI28.product_one_add_le
#print axioms NLA.MI28.determinant_normalization
#assert_trust kernel NLA.MI28.determinant_normalization
#print axioms NLA.MI28.determinant_reality_positive
#assert_trust kernel NLA.MI28.determinant_reality_positive
#print axioms NLA.MI28.determinant_comparison
#assert_trust kernel NLA.MI28.determinant_comparison
