/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial Codex assistance. Generic adaptation of the common MF14
coefficientwise smoothness proof; finite convolution avoids monomial expansion.
-/
import NLA.MF14Degree44.Family
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Algebra.Polynomial.Coeff
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
open scoped BigOperators
namespace NLA.MF14Degree44

attribute [-instance] InnerProductSpace.toNormedSpace in
def CoefficientsSmooth {n : ℕ} (F : (Fin n → ℂ) → Poly) : Prop :=
  ∀ j : ℕ, ContDiff ℂ ⊤ (fun t => (F t).coeff j)

namespace CoefficientsSmooth

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem const {n : ℕ} (p : Poly) :
    CoefficientsSmooth (fun _ : Fin n → ℂ => p) := by
  intro j
  exact contDiff_const

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem C {n : ℕ} {f : (Fin n → ℂ) → ℂ} (hf : ContDiff ℂ ⊤ f) :
    CoefficientsSmooth (fun t => Polynomial.C (f t)) := by
  intro j
  by_cases hj : j = 0
  · simpa only [coeff_C, if_pos hj] using hf
  · simp only [coeff_C, if_neg hj]
    exact contDiff_const

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem add {n : ℕ} {F G : (Fin n → ℂ) → Poly}
    (hF : CoefficientsSmooth F) (hG : CoefficientsSmooth G) :
    CoefficientsSmooth (fun t => F t + G t) := by
  intro j
  simpa only [coeff_add] using (hF j).add (hG j)

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem sub {n : ℕ} {F G : (Fin n → ℂ) → Poly}
    (hF : CoefficientsSmooth F) (hG : CoefficientsSmooth G) :
    CoefficientsSmooth (fun t => F t - G t) := by
  intro j
  simpa only [coeff_sub] using (hF j).sub (hG j)

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem mul {n : ℕ} {F G : (Fin n → ℂ) → Poly}
    (hF : CoefficientsSmooth F) (hG : CoefficientsSmooth G) :
    CoefficientsSmooth (fun t => F t * G t) := by
  intro j
  simp only [coeff_mul]
  exact ContDiff.sum (fun ij _ => (hF ij.1).mul (hG ij.2))

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem pow {n : ℕ} {F : (Fin n → ℂ) → Poly} (hF : CoefficientsSmooth F)
    (k : ℕ) : CoefficientsSmooth (fun t => F t ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using (const (n := n) (1 : Poly))
  | succ k ih => simpa only [pow_succ] using ih.mul hF

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem finsetSum {n : ℕ} {ι : Type*} (s : Finset ι)
    (F : ι → (Fin n → ℂ) → Poly) (hF : ∀ i ∈ s, CoefficientsSmooth (F i)) :
    CoefficientsSmooth (fun t => ∑ i ∈ s, F i t) := by
  intro j
  simp only [finsetSum_coeff]
  exact ContDiff.sum (fun i hi => hF i hi j)

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem linearCombination {n m : ℕ}
    (c : (Fin n → ℂ) → Fin m → ℂ) (v : (Fin n → ℂ) → Fin m → Poly)
    (hc : ∀ i, ContDiff ℂ ⊤ (fun t => c t i))
    (hv : ∀ i, CoefficientsSmooth (fun t => v t i)) :
    CoefficientsSmooth (fun t => NLA.MF14Degree44.linearCombination (c t) (v t)) := by
  intro j
  simp only [NLA.MF14Degree44.linearCombination, finsetSum_coeff]
  exact ContDiff.sum (fun i _ => ((C (hc i)).mul (hv i)) j)

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem selected {n m : ℕ} {F : (Fin n → ℂ) → Poly}
    (hF : CoefficientsSmooth F) (rows : Fin m → ℕ) :
    ContDiff ℂ ⊤ (fun t i => (F t).coeff (rows i)) := by
  apply contDiff_pi.mpr
  intro i
  exact hF (rows i)

attribute [-instance] InnerProductSpace.toNormedSpace in
theorem monicBorder {n : ℕ} (xi : (Fin n → ℂ) → Fin 7 → ℂ)
    (hxi : ∀ i, ContDiff ℂ ⊤ (fun t => xi t i)) :
    CoefficientsSmooth (fun t => monicBorderPolynomial (xi t)) := by
  have hterm (i : Fin 7) (k : ℕ) :
      CoefficientsSmooth (fun t => Polynomial.C (xi t i) * X ^ k) :=
    (C (hxi i)).mul (const (X ^ k))
  exact (((((((const (X ^ 12)).add (hterm 0 3)).add (hterm 1 6)).add
    (hterm 2 7)).add (hterm 3 8)).add (hterm 4 9)).add (hterm 5 10)).add (hterm 6 11)

end CoefficientsSmooth

#assert_trust kernel CoefficientsSmooth.const
#assert_trust kernel CoefficientsSmooth.C
#assert_trust kernel CoefficientsSmooth.add
#assert_trust kernel CoefficientsSmooth.sub
#assert_trust kernel CoefficientsSmooth.mul
#assert_trust kernel CoefficientsSmooth.pow
#assert_trust kernel CoefficientsSmooth.finsetSum
#assert_trust kernel CoefficientsSmooth.linearCombination
#assert_trust kernel CoefficientsSmooth.selected
#assert_trust kernel CoefficientsSmooth.monicBorder
end NLA.MF14Degree44
