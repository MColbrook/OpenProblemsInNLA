import NLA.MF14Degree44.ContinuationPolynomialMaps
import NLA.MF14Degree44.ContinuationCircuit
import NLA.MF14Degree44.CircuitPrefix
import Mathlib.Algebra.MvPolynomial.Monad

/- Full polynomial-equation closure transfer in all68 input and129 output
coordinates for Marcus Webb's construction. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology; Codex assistance. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.MF14Degree44

theorem continuation_closure_transfer (theta : Parameters) (z : QuadSpace)
    (hz : z ∈ jointFourClosure) :
    continuationMap theta z ∈ NLA.MF14.sevenProductClosure := by
  classical
  have heach (i : Fin 129) : ∃ P : MvPolynomial QuadIndex ℂ,
      ∀ w : QuadSpace, MvPolynomial.eval w P = continuationMap theta w i :=
    continuation_map_polynomial theta i
  choose P hP using heach
  have hpull (F : MvPolynomial (Fin 129) ℂ) (w : QuadSpace) :
      MvPolynomial.eval w (MvPolynomial.bind₁ P F) =
        MvPolynomial.eval (continuationMap theta w) F := by
    have h : (fun i => MvPolynomial.eval₂Hom (RingHom.id ℂ) w (P i)) =
        continuationMap theta w := by
      funext i
      exact hP i w
    change MvPolynomial.eval₂Hom (RingHom.id ℂ) w (MvPolynomial.bind₁ P F) = _
    rw [MvPolynomial.eval₂Hom_bind₁, h]
    rfl
  intro F hF
  have hvan : ∀ w ∈ jointFourVectors, MvPolynomial.eval w (MvPolynomial.bind₁ P F) = 0 := by
    rintro w ⟨v, hv, rfl⟩
    rw [hpull]
    have hfull := (four_prefix_full_coefficients v hv).2
    change MvPolynomial.eval
      (NLA.MF14.coefficientVector (continuationPolynomial theta (decodeQuad (quadVector v)))) F = 0
    rw [hfull]
    apply hF
    exact ⟨continuationPolynomial theta v, continuation_actual_output theta v hv, rfl⟩
  have heval := hz (MvPolynomial.bind₁ P F) hvan
  rw [hpull] at heval
  exact heval

#print axioms continuation_closure_transfer
#assert_trust kernel continuation_closure_transfer
end NLA.MF14Degree44
