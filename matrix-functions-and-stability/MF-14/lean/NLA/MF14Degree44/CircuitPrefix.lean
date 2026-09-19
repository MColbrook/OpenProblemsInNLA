/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.

Circuit-prefix semantics for the degree44 formalization of Marcus Webb's
construction. The recovered common circuit lemmas are reused with the exact
original definitions. A four-product tuple is reconstructed from all its
degree-at-most-sixteen coefficients, without dropping any polynomial tail.
-/
import NLA.MF14Degree44.Definitions
import NLA.MF14.CircuitFoundations
import Mathlib.Algebra.Polynomial.Degree.Support
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open Polynomial
open scoped BigOperators
namespace NLA.MF14Degree44

/-- The exact old at-most-seven convention is equivalent to seven padded slots. -/
theorem canonical_gate_padding (p : Poly) :
    NLA.MF14.IsAtMostSevenProductOutput p ↔ NLA.MF14.IsSevenProductOutput p := by
  exact NLA.MF14.seven_gate_padding p

/-- Only the gates before the specified prefix boundary are needed. -/
theorem prefix_gate_natDegree_bound (q : NLA.MF14.GatePolynomials) (m : ℕ)
    (hq : IsCircuitPrefix q m) (j : Fin 7) (hj : j.val < m) :
    (q j).natDegree ≤ 2 ^ (j.val + 1) := by
  have h : ∀ r : ℕ, ∀ j : Fin 7, j.val = r → j.val < m →
      (q j).natDegree ≤ 2 ^ (r + 1) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro j hjr hjm
      rcases hq.2 j hjm with ⟨u, v, hu, hv, huv⟩
      have hold (i : Fin 7) (hi : i.val < j.val) : (q i).natDegree ≤ 2 ^ r := by
        have hir : i.val < r := by omega
        have him : i.val < m := hi.trans hjm
        exact (ih i.val hir i rfl him).trans
          (pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) (by omega))
      have hd : 1 ≤ (2 : ℕ) ^ r := one_le_pow₀ (by decide)
      have hu' := NLA.MF14.natDegree_le_of_mem_available q j.val (2 ^ r) hd hold hu
      have hv' := NLA.MF14.natDegree_le_of_mem_available q j.val (2 ^ r) hd hold hv
      rw [huv]
      calc
        (u * v).natDegree ≤ u.natDegree + v.natDegree := natDegree_mul_le
        _ ≤ 2 ^ r + 2 ^ r := Nat.add_le_add hu' hv'
        _ = 2 ^ (r + 1) := by rw [pow_succ]; omega
  exact h j.val j rfl hj

/-- Every free linear combination after a prefix obeys its doubling bound. -/
theorem prefix_available_natDegree (q : NLA.MF14.GatePolynomials) (m : ℕ)
    (hq : IsCircuitPrefix q m) {p : Poly}
    (hp : p ∈ NLA.MF14.availableSpace q m) : p.natDegree ≤ 2 ^ m := by
  apply NLA.MF14.natDegree_le_of_mem_available q m (2 ^ m)
    (one_le_pow₀ (by decide : 1 ≤ (2 : ℕ))) _ hp
  intro j hj
  exact (prefix_gate_natDegree_bound q m hq j hj).trans
    (pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) (by omega))

/-- All 68 coordinates are full polynomial data for the same four-product prefix. -/
theorem four_prefix_full_coefficients (v : Quad) (hv : JointFourAvailable v) :
    (∀ i : Fin 4, (v i).natDegree ≤ 16) ∧ decodeQuad (quadVector v) = v := by
  rcases hv with ⟨q, hq, hv⟩
  have hdegree (i : Fin 4) : (v i).natDegree ≤ 16 := by
    simpa using prefix_available_natDegree q 4 hq (hv i)
  refine ⟨hdegree, ?_⟩
  funext i
  change (∑ k : Fin 17, C ((v i).coeff k.val) * X ^ k.val) = v i
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => C ((v i).coeff k) * X ^ k) 17]
  have hlt : (v i).natDegree < 17 := lt_of_le_of_lt (hdegree i) (by decide)
  exact ((v i).as_sum_range_C_mul_X_pow' hlt).symm

#print axioms canonical_gate_padding
#assert_trust kernel canonical_gate_padding
#print axioms prefix_gate_natDegree_bound
#assert_trust kernel prefix_gate_natDegree_bound
#print axioms prefix_available_natDegree
#assert_trust kernel prefix_available_natDegree
#print axioms four_prefix_full_coefficients
#assert_trust kernel four_prefix_full_coefficients

end NLA.MF14Degree44
