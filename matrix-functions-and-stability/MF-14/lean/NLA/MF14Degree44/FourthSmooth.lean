/- Smoothness of the exact fourth-product map, without derivative expansion.
Mathematical construction: Marcus Webb, The University of Manchester.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; substantial Codex assistance. -/
import NLA.MF14Degree44.CoefficientSmooth

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
namespace NLA.MF14Degree44

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem fourth_polynomial_coefficients_smooth (alpha eta gamma s lam : ℂ) :
    CoefficientsSmooth (fourthPolynomial alpha eta gamma s lam) := by
  have hterm (j : Fin 12) (p : Poly) :
      CoefficientsSmooth (fun t : Fin 12 → ℂ => C (t j) * p) :=
    (CoefficientsSmooth.C (contDiff_apply ℂ ℂ j)).mul (CoefficientsSmooth.const p)
  have hu :=
    (((CoefficientsSmooth.const (n := 12) (Rparam alpha eta gamma s)).add
      (hterm 5 X)).add (hterm 6 (X ^ 2))).add (hterm 7 (Q alpha))
  have hv :=
    ((((CoefficientsSmooth.const (n := 12) (Q alpha + C lam * X ^ 2)).add
      (hterm 8 X)).add (hterm 9 (X ^ 2))).add (hterm 10 (Q alpha))).add
      (hterm 11 (Rparam alpha eta gamma s))
  have hw :=
    ((((CoefficientsSmooth.C (contDiff_apply ℂ ℂ (0 : Fin 12))).add
      (hterm 1 X)).add (hterm 2 (X ^ 2))).add (hterm 3 (Q alpha))).add
      (hterm 4 (Rparam alpha eta gamma s))
  exact (hu.mul hv).add hw

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem fourth_map_smooth (alpha eta gamma s lam : ℂ) :
    ContDiff ℂ ⊤ (fourthCoefficientMap alpha eta gamma s lam) := by
  exact (fourth_polynomial_coefficients_smooth alpha eta gamma s lam).selected
    (fun i => (fourthRows i).val)

#print axioms fourth_polynomial_coefficients_smooth
#assert_trust kernel fourth_polynomial_coefficients_smooth
#print axioms fourth_map_smooth
#assert_trust kernel fourth_map_smooth
end NLA.MF14Degree44
