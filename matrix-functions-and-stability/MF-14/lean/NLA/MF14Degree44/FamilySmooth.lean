/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial Codex assistance. Marcus Webb retains mathematical authorship.

Smoothness follows the exact three continuation products. Each coefficient
convolution is handled symbolically by a generic lemma, without expanding
the parameter polynomial or the actual derivative/Jacobian.
-/
import NLA.MF14Degree44.CoefficientSmooth
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
namespace NLA.MF14Degree44

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem continuation_basis_coefficients_smooth (v : Parameters → Quad)
    (hv : ∀ i, CoefficientsSmooth (fun theta => v theta i)) (j : Fin 9) :
    CoefficientsSmooth (fun theta => continuationBasis theta (v theta) j) := by
  have hcomb {m : ℕ} (start : ℕ) (hstart : start + m ≤ 45)
      (b : Parameters → Fin m → Poly)
      (hb : ∀ i, CoefficientsSmooth (fun theta => b theta i)) :
      CoefficientsSmooth (fun theta =>
        linearCombination (fun i => theta (parameterIndex start hstart i)) (b theta)) :=
    CoefficientsSmooth.linearCombination _ _
      (fun i => contDiff_apply ℂ ℂ (parameterIndex start hstart i)) hb
  let l3 : Parameters → Fin 3 → Poly := fun theta => ![X, v theta 0, v theta 1]
  let l4 : Parameters → Fin 4 → Poly := fun theta => ![X, v theta 0, v theta 1, v theta 2]
  let l5 : Parameters → Fin 5 → Poly := fun theta =>
    ![X, v theta 0, v theta 1, v theta 2, v theta 3]
  have hl3 : ∀ i : Fin 3, CoefficientsSmooth (fun theta => l3 theta i) := by
    intro i
    fin_cases i
    · exact CoefficientsSmooth.const X
    · exact hv 0
    · exact hv 1
  have hl4 : ∀ i : Fin 4, CoefficientsSmooth (fun theta => l4 theta i) := by
    intro i
    fin_cases i
    · exact CoefficientsSmooth.const X
    · exact hv 0
    · exact hv 1
    · exact hv 2
  have hl5 : ∀ i : Fin 5, CoefficientsSmooth (fun theta => l5 theta i) := by
    intro i
    fin_cases i
    · exact CoefficientsSmooth.const X
    · exact hv 0
    · exact hv 1
    · exact hv 2
    · exact hv 3
  let f : Parameters → Poly := fun theta =>
    (v theta 3 + linearCombination
      (fun i : Fin 4 => theta (parameterIndex 9 (by decide) i)) (l4 theta)) *
    (v theta 2 + linearCombination
      (fun i : Fin 3 => theta (parameterIndex 13 (by decide) i)) (l3 theta))
  have hf : CoefficientsSmooth f :=
    ((hv 3).add (hcomb 9 (by decide) l4 hl4)).mul
      ((hv 2).add (hcomb 13 (by decide) l3 hl3))
  let g : Parameters → Poly := fun theta =>
    (f theta + linearCombination
      (fun i : Fin 5 => theta (parameterIndex 16 (by decide) i)) (l5 theta)) *
    (v theta 2 + linearCombination
      (fun i : Fin 3 => theta (parameterIndex 21 (by decide) i)) (l3 theta))
  have hg : CoefficientsSmooth g :=
    (hf.add (hcomb 16 (by decide) l5 hl5)).mul
      ((hv 2).add (hcomb 21 (by decide) l3 hl3))
  let l6 : Parameters → Fin 6 → Poly := fun theta =>
    ![X, v theta 0, v theta 1, v theta 2, v theta 3, f theta]
  have hl6 : ∀ i : Fin 6, CoefficientsSmooth (fun theta => l6 theta i) := by
    intro i
    fin_cases i
    · exact CoefficientsSmooth.const X
    · exact hv 0
    · exact hv 1
    · exact hv 2
    · exact hv 3
    · exact hf
  let h : Parameters → Poly := fun theta =>
    (g theta + linearCombination
      (fun i : Fin 6 => theta (parameterIndex 24 (by decide) i)) (l6 theta)) *
    (g theta + linearCombination
      (fun i : Fin 6 => theta (parameterIndex 30 (by decide) i)) (l6 theta))
  have hh : CoefficientsSmooth h :=
    (hg.add (hcomb 24 (by decide) l6 hl6)).mul (hg.add (hcomb 30 (by decide) l6 hl6))
  fin_cases j
  · exact CoefficientsSmooth.const 1
  · exact CoefficientsSmooth.const X
  · exact hv 0
  · exact hv 1
  · exact hv 2
  · exact hv 3
  · exact hf
  · exact hg
  · exact hh

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem continuation_polynomial_coefficients_smooth (v : Parameters → Quad)
    (hv : ∀ i, CoefficientsSmooth (fun theta => v theta i)) :
    CoefficientsSmooth (fun theta => continuationPolynomial theta (v theta)) := by
  exact CoefficientsSmooth.linearCombination
    (fun (theta : Parameters) (i : Fin 9) => theta (parameterIndex 36 (by decide) i))
    (fun theta => continuationBasis theta (v theta))
    (fun i => contDiff_apply ℂ ℂ (parameterIndex 36 (by decide) i))
    (continuation_basis_coefficients_smooth v hv)

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem family_quad_coefficients_smooth (i : Fin 4) :
    CoefficientsSmooth (fun theta : Parameters => familyQuad theta i) := by
  fin_cases i
  · exact CoefficientsSmooth.const (X ^ 2)
  · exact (CoefficientsSmooth.const (X ^ 4)).add
      ((CoefficientsSmooth.C (contDiff_apply ℂ ℂ (0 : Fin 45))).mul
        (CoefficientsSmooth.const (X ^ 3)))
  · exact (CoefficientsSmooth.const (X ^ 5)).add
      ((CoefficientsSmooth.C (contDiff_apply ℂ ℂ (1 : Fin 45))).mul
        (CoefficientsSmooth.const (X ^ 3)))
  · exact CoefficientsSmooth.monicBorder
      (fun (theta : Parameters) (i : Fin 7) => theta (parameterIndex 2 (by decide) i))
      (fun i => contDiff_apply ℂ ℂ (parameterIndex 2 (by decide) i))

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem family_polynomial_coefficients_smooth : CoefficientsSmooth familyPolynomial := by
  exact continuation_polynomial_coefficients_smooth familyQuad family_quad_coefficients_smooth

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem coefficient_map_smooth : ContDiff ℂ ⊤ coefficientMap := by
  exact family_polynomial_coefficients_smooth.selected (fun i : Fin 45 => i.val)

#print axioms continuation_basis_coefficients_smooth
#assert_trust kernel continuation_basis_coefficients_smooth
#print axioms continuation_polynomial_coefficients_smooth
#assert_trust kernel continuation_polynomial_coefficients_smooth
#print axioms family_quad_coefficients_smooth
#assert_trust kernel family_quad_coefficients_smooth
#print axioms family_polynomial_coefficients_smooth
#assert_trust kernel family_polynomial_coefficients_smooth
#print axioms coefficient_map_smooth
#assert_trust kernel coefficient_map_smooth
end NLA.MF14Degree44
