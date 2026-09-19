/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.

Exact structural bridges for the degree44 formalization of Marcus Webb's
construction. The matrix is the actual derivative in the standard coordinate
basis. These lemmas do not assert any numerical matrix is nonsingular.
-/
import NLA.MF14Degree44.PolynomialDensity
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF14Degree44

attribute [-instance] InnerProductSpace.toNormedSpace in
/-- The frozen coefficient Jacobian uses the actual standard basis. -/
theorem jacobianAt_eq_toMatrix (n : ℕ)
    (f : (Fin n → ℂ) → (Fin n → ℂ)) (a : Fin n → ℂ) :
    jacobianAt f a = LinearMap.toMatrix' (fderiv ℂ f a).toLinearMap := by
  ext i j
  rfl

attribute [-instance] InnerProductSpace.toNormedSpace in
/-- Matrix and continuous-linear-map determinants refer to the same derivative. -/
theorem jacobianAt_det_eq (n : ℕ)
    (f : (Fin n → ℂ) → (Fin n → ℂ)) (a : Fin n → ℂ) :
    (jacobianAt f a).det = (fderiv ℂ f a).det := by
  rw [jacobianAt_eq_toMatrix n f a]
  exact LinearMap.det_toMatrix' (fderiv ℂ f a).toLinearMap

attribute [-instance] InnerProductSpace.toNormedSpace in
/-- A separately proved nonzero Jacobian determinant gives an actual equivalence. -/
theorem derivative_equivalence_of_jacobian_det_ne_zero (n : ℕ)
    (f : (Fin n → ℂ) → (Fin n → ℂ)) (a : Fin n → ℂ)
    (hdet : (jacobianAt f a).det ≠ 0) :
    ∃ e : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ),
      (e : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) = fderiv ℂ f a := by
  have hL : (fderiv ℂ f a).det ≠ 0 := by
    rw [← jacobianAt_det_eq n f a]
    exact hdet
  exact ⟨(fderiv ℂ f a).toContinuousLinearEquivOfDetNeZero hL,
    (fderiv ℂ f a).coe_toContinuousLinearEquivOfDetNeZero hL⟩

attribute [-instance] InnerProductSpace.toNormedSpace in
/-- This conclusion concerns the derivative, not merely a stored matrix. -/
theorem derivative_bijective_of_jacobian_det_ne_zero (n : ℕ)
    (f : (Fin n → ℂ) → (Fin n → ℂ)) (a : Fin n → ℂ)
    (hdet : (jacobianAt f a).det ≠ 0) :
    Function.Bijective (fderiv ℂ f a) := by
  obtain ⟨e, he⟩ := derivative_equivalence_of_jacobian_det_ne_zero n f a hdet
  have h : Function.Bijective
      (e : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) := e.bijective
  rw [he] at h
  exact h

attribute [-instance] InnerProductSpace.toNormedSpace in
/-- Smoothness plus the actual Jacobian certificate yields polynomial density. -/
theorem polynomial_density_of_smooth_jacobian (n : ℕ)
    (f : (Fin n → ℂ) → (Fin n → ℂ)) (a : Fin n → ℂ)
    (hf : ContDiff ℂ ⊤ f) (hdet : (jacobianAt f a).det ≠ 0) :
    polynomiallyDenseRange f := by
  obtain ⟨e, he⟩ := derivative_equivalence_of_jacobian_det_ne_zero n f a hdet
  apply polynomial_density_of_strict_derivative n f a e
  rw [he]
  exact hf.hasStrictFDerivAt (by simp)

#print axioms jacobianAt_eq_toMatrix
#assert_trust kernel jacobianAt_eq_toMatrix
#print axioms jacobianAt_det_eq
#assert_trust kernel jacobianAt_det_eq
#print axioms derivative_equivalence_of_jacobian_det_ne_zero
#assert_trust kernel derivative_equivalence_of_jacobian_det_ne_zero
#print axioms derivative_bijective_of_jacobian_det_ne_zero
#assert_trust kernel derivative_bijective_of_jacobian_det_ne_zero
#print axioms polynomial_density_of_smooth_jacobian
#assert_trust kernel polynomial_density_of_smooth_jacobian

end NLA.MF14Degree44
