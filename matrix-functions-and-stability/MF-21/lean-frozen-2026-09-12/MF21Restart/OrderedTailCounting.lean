import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Logic.ExistsUnique
import Mathlib.Tactic

/-!
Finite top-down counting for a nondecreasing array. Unique ordered tail
values and coverage of every array value above the first tail value force
the original one-based label to be its actual array position plus one.
Repeated values below the tail are allowed.

The statement lock is `ORDERED_TAIL_COUNTING_STATEMENTS.md`. No analytic
or spectral claim is assumed or proved by this combinatorial component.
-/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

/-- Counting every array position above a unique tail value, including
multiplicity, identifies its one-based label without assumptions on the
lower part of the array. -/
theorem ordered_tail_index
    {α : Type*} [LinearOrder α]
    (n J : ℕ) (hJ : 1 ≤ J) (hJn : J ≤ n)
    (a : Fin n → α) (b : ℕ → α)
    (ha : Monotone a)
    (hb : StrictMonoOn b (Set.Icc J n))
    (hocc : ∀ k ∈ Set.Icc J n, ∃! i : Fin n, a i = b k)
    (hcover : ∀ i : Fin n, b J ≤ a i →
      ∃ k ∈ Set.Icc J n, a i = b k) :
    ∀ k : ℕ, ∀ hJk : J ≤ k, ∀ hkn : k ≤ n,
      a ⟨k - 1, by omega⟩ = b k := by
  classical
  let pos (ell : ℕ) (hell : ell ∈ Set.Icc J n) : Fin n :=
    (hocc ell hell).choose
  have hpos (ell : ℕ) (hell : ell ∈ Set.Icc J n) :
      a (pos ell hell) = b ell := (hocc ell hell).choose_spec.1
  intro k hJk hkn
  have hk : k ∈ Set.Icc J n := ⟨hJk, hkn⟩
  let p : Fin n := pos k hk
  have hp : a p = b k := hpos k hk
  have htail (ell : ℕ) (hell : ell ∈ Finset.Icc k n) : ell ∈ Set.Icc J n :=
    ⟨hJk.trans (Finset.mem_Icc.mp hell).1, (Finset.mem_Icc.mp hell).2⟩
  let f (ell : ℕ) (hell : ell ∈ Finset.Icc k n) : Fin n := pos ell (htail ell hell)
  have hf (ell : ℕ) (hell : ell ∈ Finset.Icc k n) : a (f ell hell) = b ell :=
    hpos ell (htail ell hell)
  have hcard : (Finset.Icc k n).card = (Finset.Ici p).card := by
    apply Finset.card_bij f
    · intro ell hell
      apply Finset.mem_Ici.mpr
      by_contra hnot
      have hlt : f ell hell < p := lt_of_not_ge hnot
      have hvalue : b ell ≤ b k := by
        rw [← hf ell hell, ← hp]
        exact ha hlt.le
      have hellk : ell ≤ k := (hb.le_iff_le (htail ell hell) hk).mp hvalue
      have heq : ell = k := le_antisymm hellk (Finset.mem_Icc.mp hell).1
      have hsame : f ell hell = p := (hocc k hk).unique (by rw [hf ell hell, heq]) hp
      exact (ne_of_lt hlt) hsame
    · intro ell hell r hr heq
      apply hb.injOn (htail ell hell) (htail r hr)
      calc
        b ell = a (f ell hell) := (hf ell hell).symm
        _ = a (f r hr) := congrArg a heq
        _ = b r := hf r hr
    · intro i hi
      have hpi : p ≤ i := Finset.mem_Ici.mp hi
      have hki : b k ≤ a i := by rw [← hp]; exact ha hpi
      have hJi : b J ≤ a i :=
        (hb.monotoneOn ⟨le_rfl, hJn⟩ hk hJk).trans hki
      obtain ⟨ell, hell, hvalue⟩ := hcover i hJi
      have hkell : k ≤ ell := (hb.le_iff_le hk hell).mp (by rw [← hvalue]; exact hki)
      have hellfin : ell ∈ Finset.Icc k n := Finset.mem_Icc.mpr ⟨hkell, hell.2⟩
      refine ⟨ell, hellfin, ?_⟩
      exact (hocc ell hell).unique (hf ell hellfin) hvalue
  have hcounts : n + 1 - k = n - p.val := by
    simpa only [Nat.card_Icc, Fin.card_Ici] using hcard
  have hpval : p.val = k - 1 := by
    have hp_lt := p.isLt
    omega
  have hpeq : p = (⟨k - 1, by omega⟩ : Fin n) := Fin.ext hpval
  simpa only [hpeq] using hp

#print axioms ordered_tail_index

end MF21Restart
