import NLA.MF14Degree44.FamilyDegreeBounds
import Mathlib.Algebra.MvPolynomial.Monad

/-!
Full ambient-space assembly helpers for Marcus Webb's degree44 construction.
These are conditional helpers; density and circuit-closure membership remain
separate obligations. Formalization: George Stepaniants, Department of Computing
and Mathematical Sciences, California Institute of Technology; Codex assistance.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.MF14Degree44

def restrict44 (z : NLA.MF14.CoefficientSpace) : Fin 45 → ℂ :=
  fun i => z ⟨i.val, i.isLt.trans (by decide)⟩

theorem degree_plane44_reconstruction (z : NLA.MF14.CoefficientSpace)
    (hz : z ∈ NLA.MF14.degreePlane 44) : embed44 (restrict44 z) = z := by
  funext i
  unfold embed44 restrict44
  split_ifs with hi
  · rfl
  · exact (hz i (by omega)).symm

def embed44Variables : Fin 129 → MvPolynomial (Fin 45) ℂ :=
  fun i => if hi : i.val < 45 then MvPolynomial.X ⟨i.val, hi⟩ else 0

theorem embed44_polynomial_pullback (F : MvPolynomial (Fin 129) ℂ) (v : Fin 45 → ℂ) :
    MvPolynomial.eval v (MvPolynomial.bind₁ embed44Variables F) =
      MvPolynomial.eval (embed44 v) F := by
  have h : (fun i => MvPolynomial.eval₂Hom (RingHom.id ℂ) v (embed44Variables i)) =
      embed44 v := by
    funext i
    unfold embed44Variables embed44
    split_ifs <;> simp
  change MvPolynomial.eval₂Hom (RingHom.id ℂ) v (MvPolynomial.bind₁ embed44Variables F) = _
  rw [MvPolynomial.eval₂Hom_bind₁, h]
  rfl

/-- Both genuine density and full original closure membership are explicit premises.
This is not the unconditional coverage contract. -/
theorem degree44_coverage_of_density_and_image
    (hdensity : polynomiallyDenseRange coefficientMap)
    (himage : ∀ theta : Parameters, fullFamilyVector theta ∈ NLA.MF14.sevenProductClosure) :
    NLA.MF14.CoversDegree 44 := by
  intro z hz F hF
  let P := MvPolynomial.bind₁ embed44Variables F
  have hP : P = 0 := by
    apply hdensity P
    intro theta
    change MvPolynomial.eval (coefficientMap theta) (MvPolynomial.bind₁ embed44Variables F) = 0
    rw [embed44_polynomial_pullback, ← (family_degree_and_full_vector theta).2]
    exact himage theta F hF
  have heval := embed44_polynomial_pullback F (restrict44 z)
  change MvPolynomial.eval (restrict44 z) P = _ at heval
  rw [hP, map_zero, degree_plane44_reconstruction z hz] at heval
  exact heval.symm

theorem original_equality_false_of_coverage44 (h44 : NLA.MF14.CoversDegree 44) :
    ¬ IsGreatest NLA.MF14.coveredDegrees 42 := by
  intro h
  have hm : 44 ∈ NLA.MF14.coveredDegrees := ⟨by decide, h44⟩
  have hh := h.2 hm
  omega

#print axioms degree_plane44_reconstruction
#assert_trust kernel degree_plane44_reconstruction
#print axioms embed44_polynomial_pullback
#assert_trust kernel embed44_polynomial_pullback
#print axioms degree44_coverage_of_density_and_image
#assert_trust kernel degree44_coverage_of_density_and_image
#print axioms original_equality_false_of_coverage44
#assert_trust kernel original_equality_false_of_coverage44

end NLA.MF14Degree44
