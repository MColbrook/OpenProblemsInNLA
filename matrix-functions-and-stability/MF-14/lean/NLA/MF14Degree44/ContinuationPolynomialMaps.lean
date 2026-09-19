import NLA.MF14Degree44.PolynomialMaps
import Mathlib.Tactic.FinCases

/- Marcus Webb's exact continuation, full coefficientwise polynomiality.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; Codex assistance. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
namespace NLA.MF14Degree44

theorem continuation_basis_coefficient_polynomial {σ : Type*} (theta : Parameters) (v : (σ → ℂ) → Quad)
    (hv : ∀ i, CoefficientPolynomial (fun z => v z i)) (j : Fin 9) :
    CoefficientPolynomial (fun z => continuationBasis theta (v z) j) := by
  have hcomb {m : ℕ} (start : ℕ) (hstart : start + m ≤ 45)
      (b : (σ → ℂ) → Fin m → Poly)
      (hb : ∀ i, CoefficientPolynomial (fun z => b z i)) :
      CoefficientPolynomial (fun z =>
        linearCombination (fun i => theta (parameterIndex start hstart i)) (b z)) :=
    CoefficientPolynomial.linearCombination _ _ hb
  let l3 : (σ → ℂ) → Fin 3 → Poly := fun z => ![X, v z 0, v z 1]
  let l4 : (σ → ℂ) → Fin 4 → Poly := fun z => ![X, v z 0, v z 1, v z 2]
  let l5 : (σ → ℂ) → Fin 5 → Poly := fun z =>
    ![X, v z 0, v z 1, v z 2, v z 3]
  have hl3 : ∀ i : Fin 3, CoefficientPolynomial (fun z => l3 z i) := by
    intro i
    fin_cases i
    · exact CoefficientPolynomial.const X
    · exact hv 0
    · exact hv 1
  have hl4 : ∀ i : Fin 4, CoefficientPolynomial (fun z => l4 z i) := by
    intro i
    fin_cases i
    · exact CoefficientPolynomial.const X
    · exact hv 0
    · exact hv 1
    · exact hv 2
  have hl5 : ∀ i : Fin 5, CoefficientPolynomial (fun z => l5 z i) := by
    intro i
    fin_cases i
    · exact CoefficientPolynomial.const X
    · exact hv 0
    · exact hv 1
    · exact hv 2
    · exact hv 3
  let f : (σ → ℂ) → Poly := fun z =>
    (v z 3 + linearCombination
      (fun i : Fin 4 => theta (parameterIndex 9 (by decide) i)) (l4 z)) *
    (v z 2 + linearCombination
      (fun i : Fin 3 => theta (parameterIndex 13 (by decide) i)) (l3 z))
  have hf : CoefficientPolynomial f :=
    ((hv 3).add (hcomb 9 (by decide) l4 hl4)).mul
      ((hv 2).add (hcomb 13 (by decide) l3 hl3))
  let g : (σ → ℂ) → Poly := fun z =>
    (f z + linearCombination
      (fun i : Fin 5 => theta (parameterIndex 16 (by decide) i)) (l5 z)) *
    (v z 2 + linearCombination
      (fun i : Fin 3 => theta (parameterIndex 21 (by decide) i)) (l3 z))
  have hg : CoefficientPolynomial g :=
    (hf.add (hcomb 16 (by decide) l5 hl5)).mul
      ((hv 2).add (hcomb 21 (by decide) l3 hl3))
  let l6 : (σ → ℂ) → Fin 6 → Poly := fun z =>
    ![X, v z 0, v z 1, v z 2, v z 3, f z]
  have hl6 : ∀ i : Fin 6, CoefficientPolynomial (fun z => l6 z i) := by
    intro i
    fin_cases i
    · exact CoefficientPolynomial.const X
    · exact hv 0
    · exact hv 1
    · exact hv 2
    · exact hv 3
    · exact hf
  let h : (σ → ℂ) → Poly := fun z =>
    (g z + linearCombination
      (fun i : Fin 6 => theta (parameterIndex 24 (by decide) i)) (l6 z)) *
    (g z + linearCombination
      (fun i : Fin 6 => theta (parameterIndex 30 (by decide) i)) (l6 z))
  have hh : CoefficientPolynomial h :=
    (hg.add (hcomb 24 (by decide) l6 hl6)).mul (hg.add (hcomb 30 (by decide) l6 hl6))
  fin_cases j
  · exact CoefficientPolynomial.const 1
  · exact CoefficientPolynomial.const X
  · exact hv 0
  · exact hv 1
  · exact hv 2
  · exact hv 3
  · exact hf
  · exact hg
  · exact hh

theorem continuation_polynomial_coefficient_polynomial {σ : Type*} (theta : Parameters) (v : (σ → ℂ) → Quad)
    (hv : ∀ i, CoefficientPolynomial (fun z => v z i)) :
    CoefficientPolynomial (fun z => continuationPolynomial theta (v z)) := by
  exact CoefficientPolynomial.linearCombination
    (fun (i : Fin 9) => theta (parameterIndex 36 (by decide) i))
    (fun z => continuationBasis theta (v z))
    (continuation_basis_coefficient_polynomial theta v hv)

theorem continuation_map_polynomial (theta : Parameters) (i : Fin 129) :
    ScalarPolynomial (fun z : QuadSpace => continuationMap theta z i) := by
  exact continuation_polynomial_coefficient_polynomial theta decodeQuad
    decodeQuad_coefficient_polynomial i.val

#print axioms continuation_basis_coefficient_polynomial
#assert_trust kernel continuation_basis_coefficient_polynomial
#print axioms continuation_polynomial_coefficient_polynomial
#assert_trust kernel continuation_polynomial_coefficient_polynomial
#print axioms continuation_map_polynomial
#assert_trust kernel continuation_map_polynomial
end NLA.MF14Degree44
