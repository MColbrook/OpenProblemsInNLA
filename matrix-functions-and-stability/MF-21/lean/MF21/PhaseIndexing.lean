import MF21.PhaseCellRoot
import MF21.TopDownIndexing

open Set
open scoped Topology
noncomputable section
namespace MF21Phase

/-- Full top-down indexing of the perturbed-sine roots. The only spectral
inputs are the zero/eigenangle correspondence and simplicity from a nonzero
determinant derivative. No information about the low eigenangles is used. -/
theorem indexed_phase_roots
    (F E dF dE : ℝ → ℝ) (D : ℝ) (hD : 0 < D) (J n : ℕ) (hJ : 1 ≤ J)
    (theta : Fin n → ℝ) (htheta : Monotone theta)
    (htheta_mem : ∀ j, theta j ∈ Ioo 0 Real.pi)
    (hF : ∀ x ∈ Icc 0 Real.pi, HasDerivAt F (dF x) x)
    (hE : ∀ x ∈ Ioo 0 Real.pi, HasDerivAt E (dE x) x)
    (hdF : ∀ x ∈ Icc 0 Real.pi, D ≤ dF x)
    (hF0 : F 0 < J*Real.pi-Real.pi/4) (hFpi : F Real.pi = (n+1)*Real.pi)
    (hsmall : ∀ x ∈ Ioo 0 Real.pi, J*Real.pi-Real.pi/4 ≤ F x →
      |E x| ≤ (1 : ℝ)/4 ∧ |dE x| ≤ D/4)
    (hspectrum : ∀ x ∈ Ioo 0 Real.pi,
      Real.sin (F x)+E x = 0 ↔ ∃ i : Fin n, theta i = x)
    (hsimple : ∀ x ∈ Ioo 0 Real.pi, Real.sin (F x)+E x = 0 →
      deriv (fun t ↦ Real.sin (F t)+E t) x ≠ 0 →
      ∀ i k : Fin n, theta i = x → theta k = x → i = k)
    (hfinal : ∀ x ∈ Ioo 0 Real.pi, |F x-(n+1)*Real.pi| ≤ Real.pi/4 →
      Real.sin (F x)+E x ≠ 0) :
    ∀ j : Fin n, J ≤ j.val+1 →
      |F (theta j)-(j.val+1)*Real.pi| ≤ Real.pi/4 ∧
      deriv (fun t ↦ Real.sin (F t)+E t) (theta j) ≠ 0 ∧
      |F (theta j)-(j.val+1)*Real.pi| ≤ (Real.pi/2)*|E (theta j)| := by
  let P (k : ℕ) (x : ℝ) : Prop := x ∈ Ioo 0 Real.pi ∧ |F x-k*Real.pi| ≤ Real.pi/4 ∧
    Real.sin (F x)+E x = 0 ∧ deriv (fun t ↦ Real.sin (F t)+E t) x ≠ 0 ∧
    ∀ y ∈ Ioo 0 Real.pi, |F y-k*Real.pi| ≤ Real.pi/4 →
      Real.sin (F y)+E y = 0 → y = x
  have hex (j : Fin n) (hj : J ≤ j.val+1) : ∃ x, P (j.val+1) x :=
    phase_tail_cell_root F E dF dE D hD J n (j.val+1) hj (by omega)
      hF hE hdF hF0 hFpi hsmall
  let r : Fin n → ℝ := fun j ↦ if hj : J ≤ j.val+1 then (hex j hj).choose else 0
  have hr (j : Fin n) (hj : J ≤ j.val+1) : P (j.val+1) (r j) := by
    dsimp only [r]
    rw [dif_pos hj]
    exact (hex j hj).choose_spec
  have hc : ContinuousOn F (Icc 0 Real.pi) :=
    fun x hx ↦ (hF x hx).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn F (Icc 0 Real.pi) := strictMonoOn_of_deriv_pos (convex_Icc _ _) hc
    (fun x hx ↦ by rw [(hF x (interior_subset hx)).deriv]; exact hD.trans_le (hdF x (interior_subset hx)))
  have hrmono : StrictMonoOn r {j | J-1 ≤ j.val} := by
    intro i hi j hj hij
    change J-1 ≤ i.val at hi
    change J-1 ≤ j.val at hj
    have hi' := hr i (by omega)
    have hj' := hr j (by omega)
    apply (hmono.lt_iff_lt ⟨le_of_lt hi'.1.1, le_of_lt hi'.1.2⟩
      ⟨le_of_lt hj'.1.1, le_of_lt hj'.1.2⟩).mp
    have hib := (abs_le.mp hi'.2.1).2
    have hjb := (abs_le.mp hj'.2.1).1
    have hij' : (i.val : ℝ)+1 ≤ j.val := by
      exact_mod_cast (show i.val+1 ≤ j.val by exact hij)
    push_cast at hib hjb
    nlinarith [Real.pi_pos]
  have hoccurs (j : Fin n) (hj : J-1 ≤ j.val) : ∃ i, theta i = r j := by
    have hh := hr j (by omega)
    exact (hspectrum _ hh.1).mp hh.2.2.1
  have hsim (j : Fin n) (hj : J-1 ≤ j.val) (i k : Fin n)
      (hi : theta i = r j) (hk : theta k = r j) : i = k := by
    have hh := hr j (by omega)
    exact hsimple _ hh.1 hh.2.2.1 hh.2.2.2.1 i k hi hk
  have hcovers (i j : Fin n) (hj : J-1 ≤ j.val) (hji : r j ≤ theta i) :
      ∃ k : Fin n, J-1 ≤ k.val ∧ theta i = r k := by
    have hrj := hr j (by omega)
    have hi := htheta_mem i
    have hic : theta i ∈ Icc 0 Real.pi := ⟨le_of_lt hi.1, le_of_lt hi.2⟩
    have hphase := hmono.monotoneOn ⟨le_of_lt hrj.1.1, le_of_lt hrj.1.2⟩ hic hji
    have hlo : J*Real.pi-Real.pi/4 ≤ F (theta i) := by
      have hb := (abs_le.mp hrj.2.1).1
      have hj' : (J : ℝ) ≤ j.val+1 := by exact_mod_cast (show J ≤ j.val+1 by omega)
      push_cast at hb
      nlinarith [Real.pi_pos]
    have hhi : F (theta i) ≤ (n+1)*Real.pi := by
      rw [← hFpi]
      exact hmono.monotoneOn hic ⟨le_of_lt Real.pi_pos, le_refl _⟩ (le_of_lt hi.2)
    have hiz : Real.sin (F (theta i))+E (theta i) = 0 := (hspectrum _ hi).mpr ⟨i, rfl⟩
    obtain ⟨k, hkJ, hkn, hkphase⟩ := root_phase_index_range _ _ J n hlo hhi
      (hsmall _ hi hlo).1 hiz
    have hkn' : k ≤ n := by
      by_contra h
      have he : k = n+1 := by omega
      rw [he, Nat.cast_add, Nat.cast_one] at hkphase
      exact hfinal _ hi (hkphase.trans (by linarith [Real.pi_pos])) hiz
    let l : Fin n := ⟨k-1, by omega⟩
    have hlk : l.val+1 = k := by dsimp [l]; omega
    have hlJ : J ≤ l.val+1 := by rwa [hlk]
    have hrl := hr l hlJ
    have hthetaeq : theta i = r l := by
      apply hrl.2.2.2.2 _ hi _ hiz
      rw [hlk]
      exact hkphase.trans (by linarith [Real.pi_pos])
    exact ⟨l, by omega, hthetaeq⟩
  have hmatch := monotone_tail_matching theta r (J-1) htheta hrmono hoccurs hsim hcovers
  intro j hj
  have heq := hmatch j (by omega)
  have hroot := hr j hj
  rw [heq]
  refine ⟨?_, hroot.2.2.2.1, ?_⟩
  · simpa only [Nat.cast_add, Nat.cast_one] using hroot.2.1
  · have hh := phase_residual_bound (F (r j)) (E (r j)) (j.val+1)
      (hroot.2.1.trans (by linarith [Real.pi_pos])) hroot.2.2.1
    simpa only [Nat.cast_add, Nat.cast_one] using hh

end MF21Phase

#print axioms MF21Phase.indexed_phase_roots
