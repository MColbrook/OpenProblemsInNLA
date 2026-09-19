/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial Codex assistance. Marcus Webb retains mathematical authorship.

Actual Fréchet derivative -> checked whole directional polynomials -> integer
matrix -> checked modular inverse -> nonsingularity over the complex numbers.
-/
import NLA.MF14Degree44.SeedFirstColumns
import NLA.MF14Degree44.JacobianNonzero
import NLA.MF14Degree44.JacobianEquivalence

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
namespace NLA.MF14Degree44

/-- D44-08c: the compact integer table is the actual complex derivative. -/
theorem coefficient_jacobian_identity :
    jacobianAt coefficientMap basePoint =
      fun i j => (integerJacobian i j : ℂ) := by
  funext i j
  rw [coefficient_jacobian_eq_first_jet, seed_first_columns]
  rw [coeff_map]
  rfl

attribute [-instance] InnerProductSpace.toNormedSpace in
/-- D44-08e: nonsingularity concerns the actual derivative with the frozen norms. -/
theorem coefficient_derivative_bijective :
    Function.Bijective (fderiv ℂ coefficientMap basePoint) := by
  apply derivative_bijective_of_jacobian_det_ne_zero 45 coefficientMap basePoint
  rw [coefficient_jacobian_identity]
  exact complex_integer_jacobian_det_ne_zero

#print axioms coefficient_jacobian_identity
#assert_trust kernel coefficient_jacobian_identity
#print axioms coefficient_derivative_bijective
#assert_trust kernel coefficient_derivative_bijective
end NLA.MF14Degree44
