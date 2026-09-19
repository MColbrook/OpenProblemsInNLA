import NLA.MF14Degree44.BorderPathContinuity
import NLA.MF14Degree44.GoodParameters
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Algebra.MvPolynomial

/- The limit step retains the full joint quad. The fourth-product density
result remains an explicit premise in this helper, pending its separate proof.
Mathematics: Marcus Webb, The University of Manchester. Formalization:
George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology; Codex assistance. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped Topology
namespace NLA.MF14Degree44

lemma joint_four_closure_isClosed : IsClosed jointFourClosure := by
  have heq : jointFourClosure =
      ⋂ F : MvPolynomial QuadIndex ℂ,
      ⋂ (_h : ∀ w ∈ jointFourVectors, MvPolynomial.eval w F = 0),
        {z | MvPolynomial.eval z F = 0} := by
    ext z
    simp only [jointFourClosure, Set.mem_setOf_eq, Set.mem_iInter]
  rw [heq]
  exact isClosed_iInter (fun F => isClosed_iInter
    (fun _ => isClosed_eq (MvPolynomial.continuous_eval F) continuous_const))

/-- Conditional assembly only: it does not discharge the fourth-product premise. -/
theorem monic_border_joint_closure_of_fourth
    (hfourth : ∀ (alpha eta gamma s : ℂ), GoodBorderParameter alpha eta gamma s →
      ∀ p : Poly, p ∈ productSpan alpha eta gamma s →
        quadVector (movingQuad alpha eta gamma s p) ∈ jointFourClosure)
    (alpha beta : ℂ) (xi : Fin 7 → ℂ) :
    quadVector (borderQuad alpha beta xi) ∈ jointFourClosure := by
  obtain ⟨gamma, hgamma⟩ :=
    IsAlgClosed.exists_pow_nat_eq ((3 * alpha - xi 6) / 4) (by decide : 0 < 2)
  have hg : 3 * alpha - 4 * gamma ^ 2 = xi 6 := by
    rw [hgamma]
    ring
  let path : ℂ → QuadSpace := fun s => quadVector (movingQuad alpha (beta + alpha ^ 2) gamma s
    (monicBorderPath alpha (beta + alpha ^ 2) gamma xi s))
  have hcont : Continuous path := moving_border_path_continuous alpha (beta + alpha ^ 2) gamma xi
  have hzero : path 0 = quadVector (borderQuad alpha beta xi) :=
    congrArg quadVector (moving_border_path_at_zero alpha beta gamma xi hg)
  have hlim : Filter.Tendsto path (nhdsWithin (0 : ℂ) ({0}ᶜ))
      (nhds (quadVector (borderQuad alpha beta xi))) := by
    have ht : Filter.Tendsto path (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds (path 0)) :=
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    rw [hzero] at ht
    exact ht
  have hevent : ∀ᶠ s in nhdsWithin (0 : ℂ) ({0}ᶜ), path s ∈ jointFourClosure := by
    filter_upwards [good_border_parameters_eventually alpha (beta + alpha ^ 2) gamma] with s hs
    exact hfourth alpha (beta + alpha ^ 2) gamma s hs
      (monicBorderPath alpha (beta + alpha ^ 2) gamma xi s)
      (monic_border_path_mem alpha (beta + alpha ^ 2) gamma xi s hs.1)
  exact joint_four_closure_isClosed.mem_of_tendsto hlim hevent

#print axioms joint_four_closure_isClosed
#assert_trust kernel joint_four_closure_isClosed
#print axioms monic_border_joint_closure_of_fourth
#assert_trust kernel monic_border_joint_closure_of_fourth
end NLA.MF14Degree44
