import NLA.MF14Degree44.SpanBasisCoordinates
import NLA.MF14Degree44.SpanReconstruction
import NLA.MF14Degree44.FourthActualCircuit
import NLA.MF14Degree44.FourthSmooth
import NLA.MF14Degree44.FourthJacobian
import NLA.MF14Degree44.FourthMinorIdentity
import NLA.MF14Degree44.JacobianEquivalence
import Mathlib.Algebra.MvPolynomial.Monad

/- Dense actual fourth-product outputs fill the literal full product span
inside joint polynomial-equation closure. Mathematics: Marcus Webb, The
University of Manchester. Formalization: George Stepaniants, Department of
Computing and Mathematical Sciences, California Institute of Technology;
Codex assistance. No previous output is discarded. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.MF14Degree44

def reconstructedMovingVector (alpha eta gamma s : ℂ) (y : Fin 12 → ℂ) : QuadSpace :=
  quadVector (movingQuad alpha eta gamma s
    (spanReconstruct (productSpanBasis alpha eta gamma s) (fun i => (fourthRows i).val) y))

lemma reconstructed_moving_coordinate_polynomial (alpha eta gamma s : ℂ) (i : QuadIndex) :
    ScalarPolynomial (fun y : Fin 12 → ℂ => reconstructedMovingVector alpha eta gamma s y i) := by
  rcases i with ⟨i, k⟩
  fin_cases i
  · exact ScalarPolynomial.const _
  · exact ScalarPolynomial.const _
  · exact ScalarPolynomial.const _
  · exact span_reconstruct_coefficient_polynomial (productSpanBasis alpha eta gamma s)
      (fun i => (fourthRows i).val) k.val

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem fourth_product_joint_closure (alpha eta gamma s : ℂ)
    (hs : GoodBorderParameter alpha eta gamma s) (p : Poly)
    (hp : p ∈ productSpan alpha eta gamma s) :
    quadVector (movingQuad alpha eta gamma s p) ∈ jointFourClosure := by
  classical
  have hdet : (basisCoefficientMatrix (productSpanBasis alpha eta gamma s)
      (fun i => (fourthRows i).val)).det ≠ 0 := by
    rw [product_basis_matrix_det]
    exact pow_ne_zero 10 hs.1
  have hreconstruct (q : Poly) (hq : q ∈ productSpan alpha eta gamma s) :
      spanReconstruct (productSpanBasis alpha eta gamma s) (fun i => (fourthRows i).val)
        (fourthCoordinates q) = q :=
    span_reconstruct_coordinates _ _ hdet q hq
  have hdensity : polynomiallyDenseRange (fourthCoefficientMap alpha eta gamma s (eta + 1)) := by
    apply polynomial_density_of_smooth_jacobian 12 _ 0
      (fourth_map_smooth alpha eta gamma s (eta + 1))
    rw [fourth_jacobian_identity, fourth_minor_identity]
    exact hs.2.2
  have heach (i : QuadIndex) : ∃ P : MvPolynomial (Fin 12) ℂ,
      ∀ y : Fin 12 → ℂ, MvPolynomial.eval y P = reconstructedMovingVector alpha eta gamma s y i :=
    reconstructed_moving_coordinate_polynomial alpha eta gamma s i
  choose P hP using heach
  have hpull (F : MvPolynomial QuadIndex ℂ) (y : Fin 12 → ℂ) :
      MvPolynomial.eval y (MvPolynomial.bind₁ P F) =
        MvPolynomial.eval (reconstructedMovingVector alpha eta gamma s y) F := by
    have h : (fun i => MvPolynomial.eval₂Hom (RingHom.id ℂ) y (P i)) =
        reconstructedMovingVector alpha eta gamma s y := by
      funext i
      exact hP i y
    change MvPolynomial.eval₂Hom (RingHom.id ℂ) y (MvPolynomial.bind₁ P F) = _
    rw [MvPolynomial.eval₂Hom_bind₁, h]
    rfl
  intro F hF
  have hzero : MvPolynomial.bind₁ P F = 0 := by
    apply hdensity
    intro t
    rw [hpull]
    change MvPolynomial.eval (quadVector (movingQuad alpha eta gamma s
      (spanReconstruct (productSpanBasis alpha eta gamma s) (fun i => (fourthRows i).val)
        (fourthCoordinates (fourthPolynomial alpha eta gamma s (eta + 1) t))))) F = 0
    rw [hreconstruct _ (fourth_polynomial_mem_product_span alpha eta gamma s (eta + 1) t)]
    apply hF
    exact ⟨movingQuad alpha eta gamma s (fourthPolynomial alpha eta gamma s (eta + 1) t),
      fourth_actual_joint alpha eta gamma s (eta + 1) hs.2.1 t, rfl⟩
  have hmap : reconstructedMovingVector alpha eta gamma s (fourthCoordinates p) =
      quadVector (movingQuad alpha eta gamma s p) := by
    unfold reconstructedMovingVector
    rw [hreconstruct p hp]
  have heval := hpull F (fourthCoordinates p)
  rw [hzero, map_zero, hmap] at heval
  exact heval.symm

#print axioms reconstructed_moving_coordinate_polynomial
#assert_trust kernel reconstructed_moving_coordinate_polynomial
#print axioms fourth_product_joint_closure
#assert_trust kernel fourth_product_joint_closure
end NLA.MF14Degree44
