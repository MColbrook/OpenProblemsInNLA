/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial Codex assistance. Basic span operations adapt the common MF14
helpers; the append lemma preserves a single chronological circuit prefix.
-/
import NLA.MF14Degree44.CircuitPrefix
import NLA.MF14Degree44.Family
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
open scoped BigOperators
namespace NLA.MF14Degree44

theorem available_one (q : NLA.MF14.GatePolynomials) (k : ℕ) :
    (1 : Poly) ∈ NLA.MF14.availableSpace q k := by
  exact Submodule.subset_span (by simp [NLA.MF14.availableGenerators])

theorem available_X (q : NLA.MF14.GatePolynomials) (k : ℕ) :
    (X : Poly) ∈ NLA.MF14.availableSpace q k := by
  exact Submodule.subset_span (by simp [NLA.MF14.availableGenerators])

theorem available_gate (q : NLA.MF14.GatePolynomials) (i : Fin 7) (k : ℕ)
    (hi : i.val < k) : q i ∈ NLA.MF14.availableSpace q k := by
  exact Submodule.subset_span (Or.inr ⟨i, hi, rfl⟩)

theorem polynomial_C_mul_mem (S : Submodule ℂ Poly) (a : ℂ) {p : Poly}
    (hp : p ∈ S) : C a * p ∈ S := by
  simpa only [smul_eq_C_mul] using S.smul_mem a hp

theorem linearCombination_mem {m : ℕ} (S : Submodule ℂ Poly)
    (c : Fin m → ℂ) (v : Fin m → Poly) (hv : ∀ i, v i ∈ S) :
    linearCombination c v ∈ S := by
  unfold linearCombination
  apply Submodule.sum_mem
  intro i _
  exact polynomial_C_mul_mem S (c i) (hv i)

theorem append_product_to_prefix (q : NLA.MF14.GatePolynomials) (j : Fin 7)
    (hq : IsCircuitPrefix q j.val) (u v : Poly)
    (hu : u ∈ NLA.MF14.availableSpace q j.val)
    (hv : v ∈ NLA.MF14.availableSpace q j.val) :
    ∃ q' : NLA.MF14.GatePolynomials,
      IsCircuitPrefix q' (j.val + 1) ∧
      NLA.MF14.availableSpace q j.val ≤ NLA.MF14.availableSpace q' (j.val + 1) ∧
      u * v ∈ NLA.MF14.availableSpace q' (j.val + 1) := by
  classical
  let q' : NLA.MF14.GatePolynomials := Function.update q j (u * v)
  have hspace (k : ℕ) (hk : k ≤ j.val) :
      NLA.MF14.availableSpace q k = NLA.MF14.availableSpace q' k := by
    apply NLA.MF14.availableSpace_congr_prefix
    intro i hi
    have hij : i ≠ j := by
      intro heq
      subst i
      omega
    simp [q', Function.update_of_ne hij]
  refine ⟨q', ?_, ?_, ?_⟩
  · refine ⟨Nat.succ_le_of_lt j.isLt, ?_⟩
    intro k hk
    by_cases hkold : k.val < j.val
    · obtain ⟨u', v', hu', hv', hprod⟩ := hq.2 k hkold
      have hkj : k ≠ j := by
        intro heq
        subst k
        omega
      refine ⟨u', v', ?_, ?_, ?_⟩
      · rwa [← hspace k.val (Nat.le_of_lt hkold)]
      · rwa [← hspace k.val (Nat.le_of_lt hkold)]
      · simpa [q', Function.update_of_ne hkj] using hprod
    · have hval : k.val = j.val := by omega
      have hkj : k = j := Fin.ext hval
      subst k
      refine ⟨u, v, ?_, ?_, ?_⟩
      · rwa [← hspace j.val le_rfl]
      · rwa [← hspace j.val le_rfl]
      · simp [q']
  · intro p hp
    apply NLA.MF14.availableSpace_mono q' (Nat.le_succ j.val)
    rwa [← hspace j.val le_rfl]
  · simpa [q'] using available_gate q' j (j.val + 1) (Nat.lt_succ_self j.val)

#print axioms available_one
#assert_trust kernel available_one
#print axioms available_X
#assert_trust kernel available_X
#print axioms available_gate
#assert_trust kernel available_gate
#print axioms polynomial_C_mul_mem
#assert_trust kernel polynomial_C_mul_mem
#print axioms linearCombination_mem
#assert_trust kernel linearCombination_mem
#print axioms append_product_to_prefix
#assert_trust kernel append_product_to_prefix
end NLA.MF14Degree44
