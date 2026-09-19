import NLA.MF14Degree44.FourthSpanMembership
import NLA.MF14Degree44.ThreeProductTuple

/- One common chronological four-product prefix retains all three prior
outputs and the actual fourth output. Mathematics: Marcus Webb. Formalization:
George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology; Codex assistance. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
namespace NLA.MF14Degree44

lemma fourth_actual_joint (alpha eta gamma s lam : ℂ)
    (hdelta : gamma * s - 2 * s ^ 2 ≠ 0) (t : Fin 12 → ℂ) :
    JointFourAvailable (movingQuad alpha eta gamma s (fourthPolynomial alpha eta gamma s lam t)) := by
  obtain ⟨q, hq, hav⟩ := three_product_tuple alpha eta gamma s hdelta
  have hx2 : (X : Poly) ^ 2 ∈ NLA.MF14.availableSpace q 3 := hav 0
  have hQ : Q alpha ∈ NLA.MF14.availableSpace q 3 := hav 1
  have hR : Rparam alpha eta gamma s ∈ NLA.MF14.availableSpace q 3 := hav 2
  obtain ⟨u, v, w, hu, hv, hw, heq⟩ :=
    fourth_polynomial_operands alpha eta gamma s lam t (NLA.MF14.availableSpace q 3)
      (available_one q 3) (available_X q 3) hx2 hQ hR
  obtain ⟨q', hq', hmono, hprod⟩ := append_product_to_prefix q (3 : Fin 7) hq u v hu hv
  refine ⟨q', hq', ?_⟩
  intro i
  fin_cases i
  · exact hmono hx2
  · exact hmono hQ
  · exact (NLA.MF14.availableSpace q' 4).sub_mem (hmono hR)
      (polynomial_C_mul_mem _ alpha (hmono hQ))
  · change fourthPolynomial alpha eta gamma s lam t ∈ NLA.MF14.availableSpace q' 4
    rw [heq]
    exact (NLA.MF14.availableSpace q' 4).add_mem hprod (hmono hw)

#print axioms fourth_actual_joint
#assert_trust kernel fourth_actual_joint
end NLA.MF14Degree44
