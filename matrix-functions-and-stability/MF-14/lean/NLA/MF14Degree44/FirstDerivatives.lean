/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.
First-derivative adaptation of the campaign's coefficientwise HessianCalculus.
No polynomial norm, truncated coefficient range, or stored derivative is assumed.
-/
import NLA.MF14Degree44.Family
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.Ring
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open Polynomial
open scoped BigOperators
namespace NLA.MF14Degree44

attribute [-instance] InnerProductSpace.toNormedSpace in
/-- All coefficients of the actual complex derivative, at every parameter point. -/
structure CoefficientDerivative {n : ℕ}
    (F D : (Fin n → ℂ) → Poly) (j : Fin n) : Prop where
  differentiable : ∀ k : ℕ, Differentiable ℂ (fun z => (F z).coeff k)
  derivative : ∀ z : Fin n → ℂ, ∀ k : ℕ,
    (fderiv ℂ (fun w => (F w).coeff k) z) (Pi.single j 1) = (D z).coeff k

namespace CoefficientDerivative

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem const {n : ℕ} (p : Poly) (j : Fin n) :
    CoefficientDerivative (fun _ => p) (fun _ => 0) j := by
  constructor
  · intro k
    exact differentiable_const _
  · intro z k
    simp

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem coordinate {n : ℕ} (i j : Fin n) :
    CoefficientDerivative (fun z => C (z i))
      (fun _ => if j = i then 1 else 0) j := by
  constructor
  · intro k
    by_cases hk : k = 0
    · simpa only [coeff_C, if_pos hk] using
        (differentiable_apply i : Differentiable ℂ (fun z : Fin n → ℂ => z i))
    · simpa only [coeff_C, if_neg hk] using
        (differentiable_const (0 : ℂ) : Differentiable ℂ (fun _ : Fin n → ℂ => (0 : ℂ)))
  · intro z k
    by_cases hk : k = 0
    · subst k
      simp only [coeff_C, if_true]
      rw [(hasFDerivAt_apply i z).fderiv]
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji, Ne.symm hji]
    · by_cases hji : j = i <;> simp [coeff_C, coeff_one, hk, hji]

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem add {n : ℕ} {F G D E : (Fin n → ℂ) → Poly} {j : Fin n}
    (hF : CoefficientDerivative F D j) (hG : CoefficientDerivative G E j) :
    CoefficientDerivative (fun z => F z + G z) (fun z => D z + E z) j := by
  constructor
  · intro k
    simpa only [coeff_add] using (hF.differentiable k).fun_add (hG.differentiable k)
  · intro z k
    simp only [coeff_add]
    rw [fderiv_fun_add (hF.differentiable k z) (hG.differentiable k z)]
    simp only [add_apply, hF.derivative, hG.derivative]

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem mul {n : ℕ} {F G D E : (Fin n → ℂ) → Poly} {j : Fin n}
    (hF : CoefficientDerivative F D j) (hG : CoefficientDerivative G E j) :
    CoefficientDerivative (fun z => F z * G z)
      (fun z => D z * G z + F z * E z) j := by
  constructor
  · intro k
    simp only [coeff_mul]
    exact Differentiable.fun_sum fun ab _ =>
      (hF.differentiable ab.1).mul (hG.differentiable ab.2)
  · intro z k
    simp only [coeff_add, coeff_mul]
    rw [fderiv_fun_sum (fun ab _ =>
      (hF.differentiable ab.1 z).mul (hG.differentiable ab.2 z))]
    simp only [sum_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ab hab
    rw [fderiv_fun_mul (hF.differentiable ab.1 z) (hG.differentiable ab.2 z)]
    simp only [add_apply, smul_apply, smul_eq_mul, hF.derivative, hG.derivative]
    ring

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem finsetSum {n : ℕ} {ι : Type*} (s : Finset ι)
    {F D : ι → (Fin n → ℂ) → Poly} {j : Fin n}
    (h : ∀ i ∈ s, CoefficientDerivative (F i) (D i) j) :
    CoefficientDerivative (fun z => ∑ i ∈ s, F i z)
      (fun z => ∑ i ∈ s, D i z) j := by
  constructor
  · intro k
    simp only [finsetSum_coeff]
    exact Differentiable.fun_sum fun i hi => (h i hi).differentiable k
  · intro z k
    simp only [finsetSum_coeff]
    rw [fderiv_fun_sum (fun i hi => (h i hi).differentiable k z)]
    simp only [sum_apply]
    exact Finset.sum_congr rfl (fun i hi => (h i hi).derivative z k)

attribute [-instance] InnerProductSpace.toNormedSpace in
/-- Finite coefficient selection is the actual vector-valued Fréchet derivative. -/
theorem selected {n m : ℕ} {F D : (Fin n → ℂ) → Poly} {j : Fin n}
    (h : CoefficientDerivative F D j) (indices : Fin m → ℕ)
    (z : Fin n → ℂ) (i : Fin m) :
    (fderiv ℂ (fun w k => (F w).coeff (indices k)) z) (Pi.single j 1) i =
      (D z).coeff (indices i) := by
  rw [fderiv_pi (fun k => h.differentiable (indices k) z)]
  exact h.derivative z (indices i)

end CoefficientDerivative

/-- Only the first derivatives needed for the density witness are stored. -/
structure PolyFirstJet (n : ℕ) where
  value : Poly
  first : Fin n → Poly

namespace PolyFirstJet

def const {n : ℕ} (p : Poly) : PolyFirstJet n := ⟨p, fun _ => 0⟩

def coordinate {n : ℕ} (z : Fin n → ℂ) (i : Fin n) : PolyFirstJet n :=
  ⟨C (z i), fun j => if j = i then 1 else 0⟩

def add {n : ℕ} (a b : PolyFirstJet n) : PolyFirstJet n :=
  ⟨a.value + b.value, fun j => a.first j + b.first j⟩

def mul {n : ℕ} (a b : PolyFirstJet n) : PolyFirstJet n :=
  ⟨a.value * b.value, fun j => a.first j * b.value + a.value * b.first j⟩

def finsetSum {n : ℕ} {ι : Type*} (s : Finset ι)
    (a : ι → PolyFirstJet n) : PolyFirstJet n :=
  ⟨∑ i ∈ s, (a i).value, fun j => ∑ i ∈ s, (a i).first j⟩

def parameterCombination {n m : ℕ} (z : Fin n → ℂ) (indices : Fin m → Fin n)
    (a : Fin m → PolyFirstJet n) : PolyFirstJet n :=
  finsetSum Finset.univ (fun i => (coordinate z (indices i)).mul (a i))

end PolyFirstJet

attribute [-instance] InnerProductSpace.toNormedSpace in
structure FirstJetSound {n : ℕ} (F : (Fin n → ℂ) → PolyFirstJet n) : Prop where
  first : ∀ j, CoefficientDerivative (fun z => (F z).value) (fun z => (F z).first j) j

namespace FirstJetSound

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem const {n : ℕ} (p : Poly) : FirstJetSound (fun _ => PolyFirstJet.const (n := n) p) := by
  exact ⟨fun j => CoefficientDerivative.const p j⟩

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem coordinate {n : ℕ} (i : Fin n) :
    FirstJetSound (fun z => PolyFirstJet.coordinate z i) := by
  exact ⟨fun j => CoefficientDerivative.coordinate i j⟩

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem add {n : ℕ} {F G : (Fin n → ℂ) → PolyFirstJet n}
    (hF : FirstJetSound F) (hG : FirstJetSound G) :
    FirstJetSound (fun z => (F z).add (G z)) := by
  exact ⟨fun j => (hF.first j).add (hG.first j)⟩

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem mul {n : ℕ} {F G : (Fin n → ℂ) → PolyFirstJet n}
    (hF : FirstJetSound F) (hG : FirstJetSound G) :
    FirstJetSound (fun z => (F z).mul (G z)) := by
  exact ⟨fun j => (hF.first j).mul (hG.first j)⟩

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem finsetSum {n : ℕ} {ι : Type*} (s : Finset ι)
    {F : ι → (Fin n → ℂ) → PolyFirstJet n}
    (h : ∀ i ∈ s, FirstJetSound (F i)) :
    FirstJetSound (fun z => PolyFirstJet.finsetSum s (fun i => F i z)) := by
  exact ⟨fun j => CoefficientDerivative.finsetSum s (fun i hi => (h i hi).first j)⟩

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem parameterCombination {n m : ℕ} (indices : Fin m → Fin n)
    {F : (Fin n → ℂ) → Fin m → PolyFirstJet n}
    (h : ∀ i, FirstJetSound (fun z => F z i)) :
    FirstJetSound (fun z => PolyFirstJet.parameterCombination z indices (F z)) := by
  exact finsetSum Finset.univ (fun i _ => (coordinate (indices i)).mul (h i))

end FirstJetSound

#assert_trust kernel CoefficientDerivative.const
#assert_trust kernel CoefficientDerivative.coordinate
#assert_trust kernel CoefficientDerivative.add
#assert_trust kernel CoefficientDerivative.mul
#assert_trust kernel CoefficientDerivative.finsetSum
#assert_trust kernel CoefficientDerivative.selected
#assert_trust kernel FirstJetSound.const
#assert_trust kernel FirstJetSound.coordinate
#assert_trust kernel FirstJetSound.add
#assert_trust kernel FirstJetSound.mul
#assert_trust kernel FirstJetSound.finsetSum
#assert_trust kernel FirstJetSound.parameterCombination

end NLA.MF14Degree44
