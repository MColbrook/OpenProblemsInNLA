/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.

A generic inverse-function-to-polynomial-density lemma for the degree44
formalization of Marcus Webb's construction. The original target definitions
and the independently approved statement are unchanged. No interval or matrix
computation is needed for this bridge.
-/
import NLA.MF14Degree44.Definitions
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Basic
import Mathlib.Analysis.Normed.Field.Basic
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped Topology
namespace NLA.MF14Degree44

attribute [-instance] InnerProductSpace.toNormedSpace in
/-- An invertible strict derivative places an open neighborhood in the range.
A polynomial vanishing on that neighborhood vanishes on a product of infinite
coordinate sets, so it is the zero polynomial. This also includes `n = 0`. -/
theorem polynomial_density_of_strict_derivative (n : ℕ)
    (f : (Fin n → ℂ) → (Fin n → ℂ)) (a : Fin n → ℂ)
    (e : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ))
    (hf : HasStrictFDerivAt f (e : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) a) :
    polynomiallyDenseRange f := by
  intro P hP
  let h := hf.toOpenPartialHomeomorph f
  have ha : f a ∈ h.target := hf.image_mem_toOpenPartialHomeomorph_target
  obtain ⟨U, hU, hbox⟩ := (isOpen_pi_iff'.mp h.open_target) (f a) ha
  have hInfinite : ∀ i : Fin n, (U i).Infinite := fun i =>
    infinite_of_mem_nhds ((f a) i) ((hU i).1.mem_nhds (hU i).2)
  apply MvPolynomial.funext_set U hInfinite
  intro x hx
  have hright : f (h.symm x) = x := by
    change h (h.symm x) = x
    exact h.right_inv (hbox hx)
  simpa only [hright, map_zero] using hP (h.symm x)

#print axioms polynomial_density_of_strict_derivative
#assert_trust kernel polynomial_density_of_strict_derivative

end NLA.MF14Degree44
