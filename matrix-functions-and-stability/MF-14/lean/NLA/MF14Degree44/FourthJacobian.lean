/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial Codex assistance. Marcus Webb retains mathematical authorship.

The complete fourth-product first jet at arbitrary complex scalar parameters.
Q and Rparam remain opaque during the twelve small exact polynomial identities.
-/
import NLA.MF14Degree44.FirstDerivatives
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
namespace NLA.MF14Degree44

def fourthFirstJet (alpha eta gamma s lam : ℂ) (t : Fin 12 → ℂ) : PolyFirstJet 12 :=
  let q := PolyFirstJet.const (n := 12) (Q alpha)
  let r := PolyFirstJet.const (n := 12) (Rparam alpha eta gamma s)
  let term (i : Fin 12) (p : Poly) :=
    (PolyFirstJet.coordinate t i).mul (PolyFirstJet.const p)
  let u := ((r.add (term 5 X)).add (term 6 (X ^ 2))).add (term 7 (Q alpha))
  let v := (((((q.add (PolyFirstJet.const (C lam * X ^ 2))).add (term 8 X)).add
    (term 9 (X ^ 2))).add (term 10 (Q alpha))).add (term 11 (Rparam alpha eta gamma s)))
  let w := ((((PolyFirstJet.coordinate t 0).add (term 1 X)).add (term 2 (X ^ 2))).add
    (term 3 (Q alpha))).add (term 4 (Rparam alpha eta gamma s))
  (u.mul v).add w

theorem fourth_first_jet_value (alpha eta gamma s lam : ℂ) (t : Fin 12 → ℂ) :
    (fourthFirstJet alpha eta gamma s lam t).value =
      fourthPolynomial alpha eta gamma s lam t := by
  rfl

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem fourth_first_jet_sound (alpha eta gamma s lam : ℂ) :
    FirstJetSound (fourthFirstJet alpha eta gamma s lam) := by
  have hterm (i : Fin 12) (p : Poly) :
      FirstJetSound (fun t =>
        (PolyFirstJet.coordinate t i).mul (PolyFirstJet.const p)) :=
    (FirstJetSound.coordinate i).mul (FirstJetSound.const p)
  have hu := (((FirstJetSound.const (n := 12) (Rparam alpha eta gamma s)).add
    (hterm 5 X)).add (hterm 6 (X ^ 2))).add (hterm 7 (Q alpha))
  have hv := (((((FirstJetSound.const (n := 12) (Q alpha)).add
    (FirstJetSound.const (C lam * X ^ 2))).add (hterm 8 X)).add
      (hterm 9 (X ^ 2))).add (hterm 10 (Q alpha))).add
        (hterm 11 (Rparam alpha eta gamma s))
  have hw := ((((FirstJetSound.coordinate (0 : Fin 12)).add (hterm 1 X)).add
    (hterm 2 (X ^ 2))).add (hterm 3 (Q alpha))).add
      (hterm 4 (Rparam alpha eta gamma s))
  exact (hu.mul hv).add hw

/-- Whole directional polynomials; no finite coefficient sampling is used. -/
theorem fourth_first_columns (alpha eta gamma s lam : ℂ) (j : Fin 12) :
    (fourthFirstJet alpha eta gamma s lam 0).first j =
      fourthDerivativeColumns alpha eta gamma s lam j := by
  fin_cases j <;>
    simp [fourthFirstJet, PolyFirstJet.const, PolyFirstJet.coordinate,
      PolyFirstJet.add, PolyFirstJet.mul, fourthDerivativeColumns]
  <;> ring

attribute [-instance] InnerProductSpace.toNormedSpace in
/-- D44-03c: the compact table is the actual derivative in the frozen row order. -/
theorem fourth_jacobian_identity (alpha eta gamma s lam : ℂ) :
    jacobianAt (fourthCoefficientMap alpha eta gamma s lam) 0 =
      fourthJacobian alpha eta gamma s lam := by
  have hvalue :
      (fun (t : Fin 12 → ℂ) (i : Fin 12) =>
        (fourthFirstJet alpha eta gamma s lam t).value.coeff (fourthRows i).val) =
      fourthCoefficientMap alpha eta gamma s lam := by
    funext t i
    change (fourthFirstJet alpha eta gamma s lam t).value.coeff (fourthRows i).val =
      (fourthPolynomial alpha eta gamma s lam t).coeff (fourthRows i).val
    rw [fourth_first_jet_value]
  funext i j
  have h := ((fourth_first_jet_sound alpha eta gamma s lam).first j).selected
    (fun i : Fin 12 => (fourthRows i).val) (0 : Fin 12 → ℂ) i
  rw [hvalue, fourth_first_columns] at h
  exact h

#print axioms fourth_first_jet_value
#assert_trust kernel fourth_first_jet_value
#print axioms fourth_first_jet_sound
#assert_trust kernel fourth_first_jet_sound
#print axioms fourth_first_columns
#assert_trust kernel fourth_first_columns
#print axioms fourth_jacobian_identity
#assert_trust kernel fourth_jacobian_identity
end NLA.MF14Degree44
