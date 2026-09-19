import NLA.MF14Degree44.Family
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.BigOperators
import LeanCert.Tactic.Verification

/-!
Polynomial-equation maps for Marcus Webb's degree44 continuation. No coordinate
or polynomial tail is dropped. Formalization: George Stepaniants, Department
of Computing and Mathematical Sciences, California Institute of Technology;
Codex assistance. These helpers assert explicit polynomials, not a new axiom.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
open scoped BigOperators
namespace NLA.MF14Degree44

def ScalarPolynomial {σ : Type*} (f : (σ → ℂ) → ℂ) : Prop :=
  ∃ P : MvPolynomial σ ℂ, ∀ z, MvPolynomial.eval z P = f z

def CoefficientPolynomial {σ : Type*} (F : (σ → ℂ) → Poly) : Prop :=
  ∀ k : ℕ, ScalarPolynomial (fun z => (F z).coeff k)

lemma ScalarPolynomial.const {σ : Type*} (c : ℂ) :
    ScalarPolynomial (fun _ : σ → ℂ => c) := by
  exact ⟨MvPolynomial.C c, fun z => MvPolynomial.eval_C c⟩

lemma ScalarPolynomial.variable {σ : Type*} (i : σ) :
    ScalarPolynomial (fun z : σ → ℂ => z i) := by
  exact ⟨MvPolynomial.X i, fun z => MvPolynomial.eval_X i⟩

lemma ScalarPolynomial.add {σ : Type*} {f g : (σ → ℂ) → ℂ}
    (hf : ScalarPolynomial f) (hg : ScalarPolynomial g) :
    ScalarPolynomial (fun z => f z + g z) := by
  obtain ⟨P, hP⟩ := hf
  obtain ⟨Q, hQ⟩ := hg
  exact ⟨P + Q, fun z => by rw [map_add, hP, hQ]⟩

lemma ScalarPolynomial.mul {σ : Type*} {f g : (σ → ℂ) → ℂ}
    (hf : ScalarPolynomial f) (hg : ScalarPolynomial g) :
    ScalarPolynomial (fun z => f z * g z) := by
  obtain ⟨P, hP⟩ := hf
  obtain ⟨Q, hQ⟩ := hg
  exact ⟨P * Q, fun z => by rw [map_mul, hP, hQ]⟩

lemma ScalarPolynomial.sum {σ ι : Type*} (s : Finset ι)
    (F : ι → (σ → ℂ) → ℂ) (hF : ∀ i, ScalarPolynomial (F i)) :
    ScalarPolynomial (fun z => ∑ i ∈ s, F i z) := by
  classical
  choose P hP using hF
  refine ⟨∑ i ∈ s, P i, ?_⟩
  intro z
  simp only [map_sum, hP]

lemma CoefficientPolynomial.const {σ : Type*} (p : Poly) :
    CoefficientPolynomial (fun _ : σ → ℂ => p) := by
  intro k
  exact ScalarPolynomial.const (p.coeff k)

lemma CoefficientPolynomial.C {σ : Type*} {f : (σ → ℂ) → ℂ}
    (hf : ScalarPolynomial f) : CoefficientPolynomial (fun z => C (f z)) := by
  intro k
  by_cases hk : k = 0
  · simpa only [coeff_C, if_pos hk] using hf
  · simpa only [coeff_C, if_neg hk] using (ScalarPolynomial.const (σ := σ) 0)

lemma CoefficientPolynomial.add {σ : Type*} {F G : (σ → ℂ) → Poly}
    (hF : CoefficientPolynomial F) (hG : CoefficientPolynomial G) :
    CoefficientPolynomial (fun z => F z + G z) := by
  intro k
  simpa only [coeff_add] using (hF k).add (hG k)

lemma CoefficientPolynomial.mul {σ : Type*} {F G : (σ → ℂ) → Poly}
    (hF : CoefficientPolynomial F) (hG : CoefficientPolynomial G) :
    CoefficientPolynomial (fun z => F z * G z) := by
  intro k
  simpa only [coeff_mul] using ScalarPolynomial.sum (Finset.antidiagonal k)
    (fun ij z => (F z).coeff ij.1 * (G z).coeff ij.2)
    (fun ij => (hF ij.1).mul (hG ij.2))

lemma CoefficientPolynomial.sum {σ ι : Type*} (s : Finset ι)
    (F : ι → (σ → ℂ) → Poly) (hF : ∀ i, CoefficientPolynomial (F i)) :
    CoefficientPolynomial (fun z => ∑ i ∈ s, F i z) := by
  intro k
  simpa only [finsetSum_coeff] using ScalarPolynomial.sum s
    (fun i z => (F i z).coeff k) (fun i => hF i k)

lemma CoefficientPolynomial.linearCombination {σ : Type*} {m : ℕ}
    (c : Fin m → ℂ) (v : (σ → ℂ) → Fin m → Poly)
    (hv : ∀ i, CoefficientPolynomial (fun z => v z i)) :
    CoefficientPolynomial (fun z => linearCombination c (v z)) := by
  exact CoefficientPolynomial.sum Finset.univ
    (fun (i : Fin m) (z : σ → ℂ) => Polynomial.C (c i) * v z i)
    (fun i => (CoefficientPolynomial.C (ScalarPolynomial.const (c i))).mul (hv i))

lemma decodeQuad_coefficient_polynomial (i : Fin 4) :
    CoefficientPolynomial (fun z : QuadSpace => decodeQuad z i) := by
  exact CoefficientPolynomial.sum Finset.univ
    (fun (k : Fin 17) (z : QuadSpace) => Polynomial.C (z (i, k)) * X ^ k.val)
    (fun k => (CoefficientPolynomial.C (ScalarPolynomial.variable (i, k))).mul
      (CoefficientPolynomial.const (X ^ k.val)))

#print axioms CoefficientPolynomial.mul
#assert_trust kernel CoefficientPolynomial.mul
#print axioms decodeQuad_coefficient_polynomial
#assert_trust kernel decodeQuad_coefficient_polynomial

end NLA.MF14Degree44
