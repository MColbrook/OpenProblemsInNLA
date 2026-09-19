/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.
Marcus Webb's integer certificate is transported exactly; no determinant is recomputed.
-/
import NLA.MF14Degree44.Mod3Certificate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF14Degree44

/-- The checked right inverse modulo three excludes an integer zero determinant. -/
theorem integer_jacobian_det_ne_zero : integerJacobian.det ≠ 0 := by
  obtain ⟨B, hB⟩ := integer_jacobian_mod3_inverse
  have hmod : integerJacobianMod3.det ≠ 0 :=
    Matrix.det_ne_zero_of_right_inverse hB
  have hcast : (integerJacobian.det : ZMod 3) = integerJacobianMod3.det := by
    have hm : integerJacobian.map (fun x : ℤ => (x : ZMod 3)) = integerJacobianMod3 := by
      ext i j
      rfl
    exact (Int.cast_det (R := ZMod 3) integerJacobian).trans (congrArg Matrix.det hm)
  intro hz
  apply hmod
  rw [← hcast, hz, Int.cast_zero]

/-- The same integer matrix is nonsingular over the actual scalar field. -/
theorem complex_integer_jacobian_det_ne_zero :
    Matrix.det (fun i j => (integerJacobian i j : ℂ)) ≠ 0 := by
  have hcast : (integerJacobian.det : ℂ) =
      Matrix.det (fun i j => (integerJacobian i j : ℂ)) := by
    exact Int.cast_det (R := ℂ) integerJacobian
  rw [← hcast]
  exact_mod_cast integer_jacobian_det_ne_zero

#print axioms integer_jacobian_det_ne_zero
#assert_trust kernel integer_jacobian_det_ne_zero
#print axioms complex_integer_jacobian_det_ne_zero
#assert_trust kernel complex_integer_jacobian_det_ne_zero

end NLA.MF14Degree44
