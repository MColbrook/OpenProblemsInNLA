import NLA.MF14.Definitions
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic

/-!
The circuit semantics and degree bound for the full MF-14 formalization.
Proof development began only after the two independent local275 statement
reviews. These lemmas do not establish the final degree-47 coverage theorem.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology.
-/

noncomputable section
open Set Polynomial
namespace NLA.MF14

lemma availableSpace_mono (q : GatePolynomials) {k l : ℕ} (hkl : k ≤ l) :
    availableSpace q k ≤ availableSpace q l := by
  apply Submodule.span_mono
  intro p hp
  rcases hp with hp | ⟨j, hj, hp⟩
  · exact Or.inl hp
  · exact Or.inr ⟨j, lt_of_lt_of_le hj hkl, hp⟩

lemma availableSpace_congr_prefix (q q' : GatePolynomials) (k : ℕ)
    (h : ∀ j : Fin 7, j.val < k → q j = q' j) :
    availableSpace q k = availableSpace q' k := by
  unfold availableSpace
  congr 1
  apply Set.ext
  intro p
  constructor
  · intro hp
    rcases hp with hp | ⟨j, hj, hp⟩
    · exact Or.inl hp
    · exact Or.inr ⟨j, hj, hp.trans (h j hj)⟩
  · intro hp
    rcases hp with hp | ⟨j, hj, hp⟩
    · exact Or.inl hp
    · exact Or.inr ⟨j, hj, hp.trans (h j hj).symm⟩

theorem seven_gate_padding (p : Poly) :
    IsAtMostSevenProductOutput p ↔ IsSevenProductOutput p := by
  classical
  constructor
  · rintro ⟨m, q, hm, hq, hp⟩
    let q' : GatePolynomials := fun j => if j.val < m then q j else 0
    have hspace (k : ℕ) (hk : k ≤ m) : availableSpace q k = availableSpace q' k := by
      apply availableSpace_congr_prefix
      intro j hj
      simp only [q', if_pos (lt_of_lt_of_le hj hk)]
    refine ⟨q', ?_, ?_⟩
    · intro k
      by_cases hk : k.val < m
      · rcases hq k hk with ⟨u, v, hu, hv, huv⟩
        refine ⟨u, v, ?_, ?_, ?_⟩
        · rwa [← hspace k.val (Nat.le_of_lt hk)]
        · rwa [← hspace k.val (Nat.le_of_lt hk)]
        · simpa only [q', if_pos hk] using huv
      · refine ⟨0, 0, (availableSpace q' k.val).zero_mem,
          (availableSpace q' k.val).zero_mem, ?_⟩
        simp only [q', if_neg hk, mul_zero]
    · apply availableSpace_mono q' hm
      rwa [← hspace m le_rfl]
  · rintro ⟨q, hq, hp⟩
    exact ⟨7, q, le_rfl, fun k _ => hq k, hp⟩

lemma natDegree_le_of_mem_available (q : GatePolynomials) (k d : ℕ)
    (hd : 1 ≤ d) (hq : ∀ j : Fin 7, j.val < k → (q j).natDegree ≤ d)
    {p : Poly} (hp : p ∈ availableSpace q k) : p.natDegree ≤ d := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      rcases hp with hp | ⟨j, hj, rfl⟩
      · rcases hp with rfl | hp
        · simpa only [natDegree_one] using Nat.zero_le d
        · have hp' : p = X := hp
          simpa only [hp', natDegree_X] using hd
      · exact hq j hj
  | zero => simpa only [natDegree_zero] using Nat.zero_le d
  | add p q _ _ hp hq => exact natDegree_add_le_of_degree_le hp hq
  | smul a p _ hp => exact (natDegree_smul_le a p).trans hp

lemma gate_natDegree_bound (q : GatePolynomials) (hq : IsSevenGateCircuit q)
    (j : Fin 7) : (q j).natDegree ≤ 2 ^ (j.val + 1) := by
  have h : ∀ m : ℕ, ∀ j : Fin 7, j.val = m →
      (q j).natDegree ≤ 2 ^ (m + 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro j hj
      rcases hq j with ⟨u, v, hu, hv, huv⟩
      have hold (i : Fin 7) (hi : i.val < j.val) : (q i).natDegree ≤ 2 ^ m := by
        have him : i.val < m := by omega
        exact (ih i.val him i rfl).trans (pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) (by omega))
      have hd : 1 ≤ (2 : ℕ) ^ m := one_le_pow₀ (by decide)
      have hu' := natDegree_le_of_mem_available q j.val (2 ^ m) hd hold hu
      have hv' := natDegree_le_of_mem_available q j.val (2 ^ m) hd hold hv
      rw [huv]
      calc
        (u * v).natDegree ≤ u.natDegree + v.natDegree := natDegree_mul_le
        _ ≤ 2 ^ m + 2 ^ m := Nat.add_le_add hu' hv'
        _ = 2 ^ (m + 1) := by rw [pow_succ]; omega
  exact h j.val j rfl

theorem circuit_degree_bound {p : Poly} (h : IsSevenProductOutput p) :
    p.natDegree ≤ 128 := by
  rcases h with ⟨q, hq, hp⟩
  apply natDegree_le_of_mem_available q 7 128 (by decide) _ hp
  intro j hj
  have hdeg := gate_natDegree_bound q hq j
  have hexp : (2 : ℕ) ^ (j.val + 1) ≤ 2 ^ 7 :=
    pow_le_pow_right' (by decide) (by omega)
  exact hdeg.trans (by simpa using hexp)

end NLA.MF14
