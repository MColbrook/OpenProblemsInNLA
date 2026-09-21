import MF21Restart.RecurrenceBasis

/-! Extension and restriction between finite recurrence equations and
full solutions satisfying the manuscript's shifted ghost constraints. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

theorem mkSol_eq_of_finite_recurrence (E : LinearRecurrence ℂ) (N : ℕ)
    (u : ℕ → ℂ)
    (hu : ∀ k < N, u (k + E.order) = ∑ i, E.coeffs i * u (k + i.val)) :
    ∀ t < N + E.order, E.mkSol (fun i => u i.val) t = u t := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro ht
    by_cases hsmall : t < E.order
    · exact E.mkSol_eq_init (fun i => u i.val) ⟨t, hsmall⟩
    · have hle : E.order ≤ t := by omega
      have hk : t - E.order < N := by omega
      have heq : t - E.order + E.order = t := Nat.sub_add_cancel hle
      calc
        E.mkSol (fun i => u i.val) t =
            ∑ i, E.coeffs i * E.mkSol (fun i => u i.val) (t - E.order + i.val) := by
          simpa only [heq] using E.is_sol_mkSol (fun i => u i.val) (t - E.order)
        _ = ∑ i, E.coeffs i * u (t - E.order + i.val) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [ih (t - E.order + i.val) (by omega) (by omega)]
        _ = u t := by simpa only [heq] using (hu (t - E.order) hk).symm

def zeroGhostExtension (m n : ℕ) (v : Fin n → ℂ) (t : ℕ) : ℂ :=
  if h : m ≤ t ∧ t < m + n then v ⟨t - m, by omega⟩ else 0

lemma zeroGhostExtension_middle (m n : ℕ) (v : Fin n → ℂ) (i : Fin n) :
    zeroGhostExtension m n v (m + i.val) = v i := by
  simp [zeroGhostExtension, i.isLt]

lemma zeroGhostExtension_lower (m n : ℕ) (v : Fin n → ℂ) (i : Fin m) :
    zeroGhostExtension m n v i.val = 0 := by
  simp [zeroGhostExtension, show ¬m ≤ i.val by omega]

lemma zeroGhostExtension_upper (m n : ℕ) (v : Fin n → ℂ) (i : Fin m) :
    zeroGhostExtension m n v (n + m + i.val) = 0 := by
  simp [zeroGhostExtension, show ¬n + m + i.val < m + n by omega]

lemma zeroGhostExtension_eq_of_ghosts (m n : ℕ) (u : ℕ → ℂ)
    (hlower : ∀ i : Fin m, u i.val = 0)
    (hupper : ∀ i : Fin m, u (n + m + i.val) = 0) :
    ∀ t < n + 2 * m,
      zeroGhostExtension m n (fun i => u (m + i.val)) t = u t := by
  intro t ht
  by_cases hlow : t < m
  · rw [show zeroGhostExtension m n (fun i => u (m + i.val)) t = 0 by
      exact zeroGhostExtension_lower m n _ ⟨t, hlow⟩]
    exact (hlower ⟨t, hlow⟩).symm
  · by_cases hmid : t < m + n
    · have hle : m ≤ t := by omega
      have hinterval : m ≤ t ∧ t < m + n := ⟨hle, hmid⟩
      simp only [zeroGhostExtension, dif_pos hinterval]
      congr 1
      omega
    · have hi : t - (n + m) < m := by omega
      have heq : n + m + (t - (n + m)) = t := by omega
      have hz := hupper ⟨t - (n + m), hi⟩
      rw [heq] at hz
      simp [zeroGhostExtension, hmid, hz]

theorem finite_recurrence_iff_ghost_solution
    (m n : ℕ) (a : Fin (2 * m) → ℂ) :
    (∃ v : Fin n → ℂ, v ≠ 0 ∧ ∀ k : Fin n,
      zeroGhostExtension m n v (k.val + 2 * m) =
        ∑ i, a i * zeroGhostExtension m n v (k.val + i.val)) ↔
    (∃ u : ℕ → ℂ, (LinearRecurrence.mk (2 * m) a).IsSolution u ∧ u ≠ 0 ∧
      (∀ i : Fin m, u i.val = 0) ∧ (∀ i : Fin m, u (n + m + i.val) = 0)) := by
  let E := LinearRecurrence.mk (2 * m) a
  constructor
  · rintro ⟨v, hv, hrec⟩
    let u := E.mkSol (fun i => zeroGhostExtension m n v i.val)
    have heq : ∀ t < n + 2 * m, u t = zeroGhostExtension m n v t := by
      apply mkSol_eq_of_finite_recurrence E n (zeroGhostExtension m n v)
      intro k hk
      exact hrec ⟨k, hk⟩
    refine ⟨u, E.is_sol_mkSol _, ?_, ?_, ?_⟩
    · intro hz
      apply hv
      funext i
      have hi := heq (m + i.val) (by omega)
      simpa only [zeroGhostExtension_middle, hz, Pi.zero_apply] using hi.symm
    · intro i
      rw [heq i.val (by omega)]
      exact zeroGhostExtension_lower m n v i
    · intro i
      rw [heq (n + m + i.val) (by omega)]
      exact zeroGhostExtension_upper m n v i
  · rintro ⟨u, hu, hune, hlower, hupper⟩
    let v : Fin n → ℂ := fun i => u (m + i.val)
    have heq : ∀ t < n + 2 * m, zeroGhostExtension m n v t = u t :=
      zeroGhostExtension_eq_of_ghosts m n u hlower hupper
    refine ⟨v, ?_, ?_⟩
    · intro hv
      apply hune
      apply (E.eq_iff_eqOn_range_order u 0 hu (by intro k; simp)).mpr
      intro t ht
      have htrange : t < 2 * m := Finset.mem_range.mp ht
      have h := heq t (by omega)
      rw [hv] at h
      simpa [zeroGhostExtension] using h.symm
    · intro k
      rw [heq (k.val + 2 * m) (by omega)]
      calc
        u (k.val + 2 * m) = ∑ i, a i * u (k.val + i.val) := hu k.val
        _ = ∑ i, a i * zeroGhostExtension m n v (k.val + i.val) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [heq (k.val + i.val) (by omega)]

#print axioms mkSol_eq_of_finite_recurrence
#print axioms finite_recurrence_iff_ghost_solution

end MF21Restart
