/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial Codex assistance. Marcus Webb retains mathematical authorship.

The factored first jet mirrors the frozen family without expanding parameter
monomials. Its value and derivatives are separately linked to actual functions.
-/
import NLA.MF14Degree44.FirstDerivatives
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
open scoped BigOperators
namespace NLA.MF14Degree44

abbrev FirstJet := PolyFirstJet 45

/-- Same seven monic coefficients and the same parameter coordinates as the frozen family. -/
def familyFirstQuad (theta : Parameters) : Fin 4 → FirstJet :=
  let q := (PolyFirstJet.const (X ^ 4)).add
    ((PolyFirstJet.coordinate theta 0).mul (PolyFirstJet.const (X ^ 3)))
  let r := (PolyFirstJet.const (X ^ 5)).add
    ((PolyFirstJet.coordinate theta 1).mul (PolyFirstJet.const (X ^ 3)))
  let term (i : Fin 7) (k : ℕ) :=
    (PolyFirstJet.coordinate theta (parameterIndex 2 (by decide) i)).mul
      (PolyFirstJet.const (X ^ k))
  let p := (((((((PolyFirstJet.const (X ^ 12)).add (term 0 3)).add
    (term 1 6)).add (term 2 7)).add (term 3 8)).add (term 4 9)).add
      (term 5 10)).add (term 6 11)
  ![PolyFirstJet.const (X ^ 2), q, r, p]

def continuationFirstBasis (theta : Parameters) (v : Fin 4 → FirstJet) : Fin 9 → FirstJet :=
  let q := v 1
  let r := v 2
  let p := v 3
  let l3 : Fin 3 → FirstJet := ![PolyFirstJet.const X, v 0, q]
  let l4 : Fin 4 → FirstJet := ![PolyFirstJet.const X, v 0, q, r]
  let l5 : Fin 5 → FirstJet := ![PolyFirstJet.const X, v 0, q, r, p]
  let f :=
    (p.add (PolyFirstJet.parameterCombination theta (parameterIndex 9 (by decide)) l4)).mul
    (r.add (PolyFirstJet.parameterCombination theta (parameterIndex 13 (by decide)) l3))
  let g :=
    (f.add (PolyFirstJet.parameterCombination theta (parameterIndex 16 (by decide)) l5)).mul
    (r.add (PolyFirstJet.parameterCombination theta (parameterIndex 21 (by decide)) l3))
  let l6 : Fin 6 → FirstJet := ![PolyFirstJet.const X, v 0, q, r, p, f]
  let h :=
    (g.add (PolyFirstJet.parameterCombination theta (parameterIndex 24 (by decide)) l6)).mul
    (g.add (PolyFirstJet.parameterCombination theta (parameterIndex 30 (by decide)) l6))
  ![PolyFirstJet.const 1, PolyFirstJet.const X, v 0, q, r, p, f, g, h]

def familyFirstJet (theta : Parameters) : FirstJet :=
  PolyFirstJet.parameterCombination theta (parameterIndex 36 (by decide))
    (continuationFirstBasis theta (familyFirstQuad theta))

theorem family_first_quad_value (theta : Parameters) (i : Fin 4) :
    (familyFirstQuad theta i).value = familyQuad theta i := by
  fin_cases i <;> rfl

theorem continuation_first_basis_value (theta : Parameters) (v : Fin 4 → FirstJet)
    (i : Fin 9) :
    (continuationFirstBasis theta v i).value =
      continuationBasis theta (fun j => (v j).value) i := by
  fin_cases i <;>
    simp [continuationFirstBasis, continuationBasis, PolyFirstJet.const,
      PolyFirstJet.add, PolyFirstJet.mul, PolyFirstJet.coordinate,
      PolyFirstJet.parameterCombination, PolyFirstJet.finsetSum,
      linearCombination, Fin.sum_univ_succ]

theorem family_first_jet_value (theta : Parameters) :
    (familyFirstJet theta).value = familyPolynomial theta := by
  change (∑ i : Fin 9, C (theta (parameterIndex 36 (by decide) i)) *
      (continuationFirstBasis theta (familyFirstQuad theta) i).value) =
    linearCombination (fun i : Fin 9 => theta (parameterIndex 36 (by decide) i))
      (continuationBasis theta (familyQuad theta))
  have hv : (fun i => (familyFirstQuad theta i).value) = familyQuad theta :=
    funext (family_first_quad_value theta)
  simp only [continuation_first_basis_value, hv, linearCombination]

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem family_first_quad_sound (i : Fin 4) :
    FirstJetSound (fun theta => familyFirstQuad theta i) := by
  have hterm (j : Fin 7) (k : ℕ) :
      FirstJetSound (fun theta : Parameters =>
        (PolyFirstJet.coordinate theta (parameterIndex 2 (by decide) j)).mul
          (PolyFirstJet.const (X ^ k))) :=
    (FirstJetSound.coordinate _).mul (FirstJetSound.const _)
  fin_cases i
  · exact FirstJetSound.const (X ^ 2)
  · exact (FirstJetSound.const (X ^ 4)).add
      ((FirstJetSound.coordinate (0 : Fin 45)).mul (FirstJetSound.const (X ^ 3)))
  · exact (FirstJetSound.const (X ^ 5)).add
      ((FirstJetSound.coordinate (1 : Fin 45)).mul (FirstJetSound.const (X ^ 3)))
  · exact (((((((FirstJetSound.const (X ^ 12)).add (hterm 0 3)).add
      (hterm 1 6)).add (hterm 2 7)).add (hterm 3 8)).add (hterm 4 9)).add
        (hterm 5 10)).add (hterm 6 11)

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem continuation_first_basis_sound (v : Parameters → Fin 4 → FirstJet)
    (hv : ∀ i, FirstJetSound (fun theta => v theta i)) (j : Fin 9) :
    FirstJetSound (fun theta => continuationFirstBasis theta (v theta) j) := by
  have hcomb {m : ℕ} (start : ℕ) (hstart : start + m ≤ 45)
      (b : Parameters → Fin m → FirstJet)
      (hb : ∀ i, FirstJetSound (fun theta => b theta i)) :
      FirstJetSound (fun theta =>
        PolyFirstJet.parameterCombination theta (parameterIndex start hstart) (b theta)) :=
    FirstJetSound.parameterCombination _ hb
  let l3 : Parameters → Fin 3 → FirstJet := fun theta =>
    ![PolyFirstJet.const X, v theta 0, v theta 1]
  let l4 : Parameters → Fin 4 → FirstJet := fun theta =>
    ![PolyFirstJet.const X, v theta 0, v theta 1, v theta 2]
  let l5 : Parameters → Fin 5 → FirstJet := fun theta =>
    ![PolyFirstJet.const X, v theta 0, v theta 1, v theta 2, v theta 3]
  have hl3 : ∀ i : Fin 3, FirstJetSound (fun theta => l3 theta i) := by
    intro i
    fin_cases i
    · exact FirstJetSound.const X
    · exact hv 0
    · exact hv 1
  have hl4 : ∀ i : Fin 4, FirstJetSound (fun theta => l4 theta i) := by
    intro i
    fin_cases i
    · exact FirstJetSound.const X
    · exact hv 0
    · exact hv 1
    · exact hv 2
  have hl5 : ∀ i : Fin 5, FirstJetSound (fun theta => l5 theta i) := by
    intro i
    fin_cases i
    · exact FirstJetSound.const X
    · exact hv 0
    · exact hv 1
    · exact hv 2
    · exact hv 3
  let f : Parameters → FirstJet := fun theta =>
    ((v theta 3).add (PolyFirstJet.parameterCombination theta
      (parameterIndex 9 (by decide)) (l4 theta))).mul
    ((v theta 2).add (PolyFirstJet.parameterCombination theta
      (parameterIndex 13 (by decide)) (l3 theta)))
  have hf : FirstJetSound f :=
    ((hv 3).add (hcomb 9 (by decide) l4 hl4)).mul
      ((hv 2).add (hcomb 13 (by decide) l3 hl3))
  let g : Parameters → FirstJet := fun theta =>
    ((f theta).add (PolyFirstJet.parameterCombination theta
      (parameterIndex 16 (by decide)) (l5 theta))).mul
    ((v theta 2).add (PolyFirstJet.parameterCombination theta
      (parameterIndex 21 (by decide)) (l3 theta)))
  have hg : FirstJetSound g :=
    (hf.add (hcomb 16 (by decide) l5 hl5)).mul
      ((hv 2).add (hcomb 21 (by decide) l3 hl3))
  let l6 : Parameters → Fin 6 → FirstJet := fun theta =>
    ![PolyFirstJet.const X, v theta 0, v theta 1, v theta 2, v theta 3, f theta]
  have hl6 : ∀ i : Fin 6, FirstJetSound (fun theta => l6 theta i) := by
    intro i
    fin_cases i
    · exact FirstJetSound.const X
    · exact hv 0
    · exact hv 1
    · exact hv 2
    · exact hv 3
    · exact hf
  let h : Parameters → FirstJet := fun theta =>
    ((g theta).add (PolyFirstJet.parameterCombination theta
      (parameterIndex 24 (by decide)) (l6 theta))).mul
    ((g theta).add (PolyFirstJet.parameterCombination theta
      (parameterIndex 30 (by decide)) (l6 theta)))
  have hh : FirstJetSound h :=
    (hg.add (hcomb 24 (by decide) l6 hl6)).mul (hg.add (hcomb 30 (by decide) l6 hl6))
  fin_cases j
  · exact FirstJetSound.const 1
  · exact FirstJetSound.const X
  · exact hv 0
  · exact hv 1
  · exact hv 2
  · exact hv 3
  · exact hf
  · exact hg
  · exact hh

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem family_first_jet_sound : FirstJetSound familyFirstJet := by
  exact FirstJetSound.parameterCombination _
    (continuation_first_basis_sound familyFirstQuad family_first_quad_sound)

attribute [-instance] InnerProductSpace.toNormedSpace in
/-- This is the actual coefficient map's derivative; no seed table is substituted here. -/
theorem coefficient_jacobian_eq_first_jet (theta : Parameters) (i j : Fin 45) :
    jacobianAt coefficientMap theta i j = ((familyFirstJet theta).first j).coeff i.val := by
  have hvalue :
      (fun (w : Parameters) (k : Fin 45) => (familyFirstJet w).value.coeff k.val) =
        coefficientMap := by
    funext w k
    change (familyFirstJet w).value.coeff k.val = (familyPolynomial w).coeff k.val
    rw [family_first_jet_value]
  have h := (family_first_jet_sound.first j).selected
    (fun i : Fin 45 => i.val) theta i
  rw [hvalue] at h
  exact h

#print axioms family_first_jet_value
#assert_trust kernel family_first_jet_value
#print axioms family_first_jet_sound
#assert_trust kernel family_first_jet_sound
#print axioms coefficient_jacobian_eq_first_jet
#assert_trust kernel coefficient_jacobian_eq_first_jet
end NLA.MF14Degree44
