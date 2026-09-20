import MF21.Eigenangles

/-! The finite counting argument that identifies phase roots by their actual
increasing eigenvalue indices, without any assertion about lower roots. -/

open Set
namespace MF21Phase

theorem monotone_tail_matching {n : ℕ} (theta r : Fin n → ℝ) (J : ℕ)
    (htheta : Monotone theta) (hr : StrictMonoOn r {j | J ≤ j.val})
    (hoccurs : ∀ j : Fin n, J ≤ j.val → ∃ i : Fin n, theta i = r j)
    (hsimple : ∀ j : Fin n, J ≤ j.val → ∀ i k : Fin n,
      theta i = r j → theta k = r j → i = k)
    (hcovers : ∀ i j : Fin n, J ≤ j.val → r j ≤ theta i →
      ∃ k : Fin n, J ≤ k.val ∧ theta i = r k) :
    ∀ j : Fin n, J ≤ j.val → theta j = r j := by
  cases n with
  | zero => intro j; exact Fin.elim0 j
  | succ n =>
    intro j
    induction j using Fin.reverseInduction with
    | last =>
      intro hj
      obtain ⟨i, hi⟩ := hoccurs (Fin.last n) hj
      have hlo : r (Fin.last n) ≤ theta (Fin.last n) := by
        rw [← hi]
        exact htheta (Fin.le_last i)
      obtain ⟨k, hk, he⟩ := hcovers (Fin.last n) (Fin.last n) hj hlo
      have hhi : theta (Fin.last n) ≤ r (Fin.last n) := by
        rw [he]
        exact hr.monotoneOn hk hj (Fin.le_last k)
      exact le_antisymm hhi hlo
    | cast j ih =>
      intro hj
      have hj' : J ≤ j.succ.val := by simpa using Nat.le_trans hj (Nat.le_succ j.val)
      have hnext := ih hj'
      have hrr : r j.castSucc < r j.succ := hr hj hj' Fin.castSucc_lt_succ
      obtain ⟨i, hi⟩ := hoccurs j.castSucc hj
      have hij : i ≤ j.castSucc := by
        by_contra h
        have hji : j.succ ≤ i := by
          simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at *
          omega
        have hh := htheta hji
        rw [hnext, hi] at hh
        linarith
      have hlo : r j.castSucc ≤ theta j.castSucc := by rw [← hi]; exact htheta hij
      obtain ⟨k, hk, he⟩ := hcovers j.castSucc j.castSucc hj hlo
      have hkj : k ≤ j.castSucc := by
        by_contra h
        have hsk : j.succ ≤ k := by
          simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at *
          omega
        have hlow : r j.succ ≤ theta j.castSucc := by
          rw [he]
          exact hr.monotoneOn hj' hk hsk
        have hhigh : theta j.castSucc ≤ r j.succ := by
          rw [← hnext]
          exact htheta (le_of_lt Fin.castSucc_lt_succ)
        have heq := hsimple j.succ hj' j.castSucc j.succ (le_antisymm hhigh hlow) hnext
        exact (ne_of_lt Fin.castSucc_lt_succ) heq
      have hhi : theta j.castSucc ≤ r j.castSucc := by
        rw [he]
        exact hr.monotoneOn hk hj hkj
      exact le_antisymm hhi hlo

end MF21Phase

#print axioms MF21Phase.monotone_tail_matching
