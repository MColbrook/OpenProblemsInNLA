import MF21Restart.OrderedTailCounting
import MF21Restart.SpectralOrder
import MF21Restart.PhaseWindowRoots
import MF21Restart.PhaseRootCoverage

/-!
The actual high phase labels equal the original one-based sorted eigenvalue
indices. All hypotheses of the finite tail-counting theorem are discharged
using the actual symbol, spectrum, residual roots, and coverage theorem.
The root family is local to the proof, not a new trusted definition.

The statement lock is `PHASE_WINDOW_INDEXING_STATEMENTS.md`. Quantitative
distances from exact phase-grid preimages remain a separate step.
-/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

private theorem eigenvalue_of_fin_index (m n : ℕ) (i : Fin n) :
    eigenvalue m n (i.val + 1) = orderedEigenvalue m n i := by
  simpa only [Nat.add_sub_cancel] using
    (eigenvalue_in_range (m := m) (n := n) (j := i.val + 1)
      (by omega) (by have := i.isLt; omega))

private theorem unique_fin_index_of_unique_one_based
    (m n : ℕ) (lam : ℝ)
    (h : ∃! j : ℕ, 1 ≤ j ∧ j ≤ n ∧ eigenvalue m n j = lam) :
    ∃! i : Fin n, orderedEigenvalue m n i = lam := by
  obtain ⟨j, hj, hunique⟩ := h
  let i : Fin n := ⟨j - 1, by omega⟩
  refine ⟨i, ?_, ?_⟩
  · have hv := hj.2.2
    rw [eigenvalue_in_range hj.1 hj.2.1] at hv
    exact hv
  · intro r hr
    have hrn : r.val + 1 ≤ n := by have := r.isLt; omega
    have hrvalue : eigenvalue m n (r.val + 1) = lam :=
      (eigenvalue_of_fin_index m n r).trans hr
    have heq := hunique (r.val + 1) ⟨by omega, hrn, hrvalue⟩
    apply Fin.ext
    dsimp only [i]
    omega

/-- Adjacent closed quarter-period cells still have a strict half-period
gap, so all phase values respect their natural labels. -/
private theorem phase_cells_ordered (k ell : ℕ) (hkl : k < ell) (x y : ℝ)
    (hx : |x - (k : ℝ) * Real.pi| ≤ Real.pi / 4)
    (hy : |y - (ell : ℝ) * Real.pi| ≤ Real.pi / 4) : x < y := by
  have hstep : (k : ℝ) + 1 ≤ ell := by exact_mod_cast (show k + 1 ≤ ell by omega)
  have hmul := mul_le_mul_of_nonneg_right hstep Real.pi_pos.le
  have hxupper := (abs_le.mp hx).2
  have hylower := (abs_le.mp hy).1
  nlinarith only [hmul, hxupper, hylower, Real.pi_pos]

/-- The label in the actual phase window is the published one-based
eigenvalue index, with a simple actual residual zero in that window. -/
theorem eigenvalue_eventual_phase_window (m : ℕ) (hm : 2 ≤ m) :
    ∃ N J : ℕ, 1 ≤ N ∧ 1 ≤ J ∧
      ∀ n : ℕ, N ≤ n → ∀ j : ℕ, J ≤ j → j ≤ n →
        ∃ θ : ℝ, θ ∈ Set.Ioo 0 Real.pi ∧
          symbol m θ = eigenvalue m n j ∧
          |manuscriptPhaseFn m n θ - (j : ℝ) * Real.pi| ≤ Real.pi / 4 ∧
          manuscriptResidual m n hm θ = 0 ∧
          deriv (manuscriptResidual m n hm) θ ≠ 0 := by
  classical
  obtain ⟨Nw, Jw, hNw, hJw, hw⟩ := manuscriptResidual_unique_root_in_phase_windows m hm
  obtain ⟨Nc, Jc, hNc, hJc, hc⟩ := manuscriptResidual_high_phase_root_coverage m hm
  obtain ⟨Nm, hmono⟩ := manuscriptPhaseFn_eventual_strictMonoOn m (by omega)
  let J : ℕ := max Jw Jc
  let N : ℕ := max (max Nw Nc) (max Nm J)
  have hJ1 : 1 ≤ J := hJw.trans (le_max_left Jw Jc)
  have hN1 : 1 ≤ N := hNw.trans
    ((le_max_left Nw Nc).trans (le_max_left (max Nw Nc) (max Nm J)))
  refine ⟨N, J, hN1, hJ1, ?_⟩
  intro n hn
  have hnW : Nw ≤ n := (le_max_left Nw Nc).trans
    ((le_max_left (max Nw Nc) (max Nm J)).trans hn)
  have hnC : Nc ≤ n := (le_max_right Nw Nc).trans
    ((le_max_left (max Nw Nc) (max Nm J)).trans hn)
  have hnM : Nm ≤ n := (le_max_left Nm J).trans
    ((le_max_right (max Nw Nc) (max Nm J)).trans hn)
  have hnJ : J ≤ n := (le_max_right Nm J).trans
    ((le_max_right (max Nw Nc) (max Nm J)).trans hn)
  have hJW : Jw ≤ J := le_max_left Jw Jc
  have hJC : Jc ≤ J := le_max_right Jw Jc
  have hFmono := hmono n hnM
  have hgmono := symbol_strictMonoOn m (by omega)
  let root : ℕ → ℝ := fun k =>
    if hk : k ∈ Set.Icc J n then
      (hw n hnW k (hJW.trans hk.1) hk.2).1.choose
    else 0
  have hroot (k : ℕ) (hk : k ∈ Set.Icc J n) :
      root k ∈ Set.Ioo 0 Real.pi ∧
        |manuscriptPhaseFn m n (root k) - (k : ℝ) * Real.pi| ≤ Real.pi / 4 ∧
        manuscriptResidual m n hm (root k) = 0 := by
    simp only [root, dif_pos hk]
    exact (hw n hnW k (hJW.trans hk.1) hk.2).1.choose_spec.1
  have hrootDeriv (k : ℕ) (hk : k ∈ Set.Icc J n) :
      deriv (manuscriptResidual m n hm) (root k) ≠ 0 :=
    (hw n hnW k (hJW.trans hk.1) hk.2).2 (root k) (hroot k hk).1 (hroot k hk).2.1
  have hrootMono : StrictMonoOn root (Set.Icc J n) := by
    intro k hk ell hell hkl
    have hx := hroot k hk
    have hy := hroot ell hell
    have hphase := phase_cells_ordered k ell hkl
      (manuscriptPhaseFn m n (root k)) (manuscriptPhaseFn m n (root ell)) hx.2.1 hy.2.1
    exact (hFmono.lt_iff_lt ⟨hx.1.1.le, hx.1.2.le⟩
      ⟨hy.1.1.le, hy.1.2.le⟩).mp hphase
  let b : ℕ → ℝ := fun k => symbol m (root k)
  have hb : StrictMonoOn b (Set.Icc J n) := by
    intro k hk ell hell hkl
    exact hgmono ⟨(hroot k hk).1.1.le, (hroot k hk).1.2.le⟩
      ⟨(hroot ell hell).1.1.le, (hroot ell hell).1.2.le⟩ (hrootMono hk hell hkl)
  have hocc (k : ℕ) (hk : k ∈ Set.Icc J n) :
      ∃! i : Fin n, orderedEigenvalue m n i = b k := by
    apply unique_fin_index_of_unique_one_based m n (b k)
    exact manuscriptResidual_simple_zero_existsUnique_eigenvalue_index m n hm
      (root k) (hroot k hk).1.1 (hroot k hk).1.2 (hroot k hk).2.2 (hrootDeriv k hk)
  have hcover (i : Fin n) (hi : b J ≤ orderedEigenvalue m n i) :
      ∃ k ∈ Set.Icc J n, orderedEigenvalue m n i = b k := by
    have hi1 : 1 ≤ i.val + 1 := by omega
    have hin : i.val + 1 ≤ n := by have := i.isLt; omega
    obtain ⟨θ, hθ, hvalue⟩ :=
      (eigenvalue_existsUnique_angle m n (i.val + 1) (by omega) hi1 hin).exists
    rw [eigenvalue_of_fin_index m n i] at hvalue
    have hJroot := hroot J ⟨le_rfl, hnJ⟩
    have hθJ : root J ≤ θ :=
      (hgmono.le_iff_le ⟨hJroot.1.1.le, hJroot.1.2.le⟩
        ⟨hθ.1.le, hθ.2.le⟩).mp (by
          rw [hvalue]
          exact hi)
    have hphaseOrder : manuscriptPhaseFn m n (root J) ≤ manuscriptPhaseFn m n θ :=
      hFmono.monotoneOn ⟨hJroot.1.1.le, hJroot.1.2.le⟩ ⟨hθ.1.le, hθ.2.le⟩ hθJ
    have hthreshold : (Jc : ℝ) * Real.pi - Real.pi / 4 ≤ manuscriptPhaseFn m n θ := by
      have hJcr : (Jc : ℝ) ≤ J := by exact_mod_cast hJC
      have hmul := mul_le_mul_of_nonneg_right hJcr Real.pi_pos.le
      linarith only [hmul, hphaseOrder, (abs_le.mp hJroot.2.1).1]
    have hzero : manuscriptResidual m n hm θ = 0 := by
      change Real.sin (manuscriptPhaseFn m n θ) + manuscriptError m n hm θ = 0
      apply (eigenvalue_iff_sin_add_manuscriptError_zero m n hm θ hθ.1 hθ.2).mp
      exact ⟨i.val + 1, hi1, hin, (eigenvalue_of_fin_index m n i).trans hvalue.symm⟩
    obtain ⟨ell, hCellLower, helln, hcell⟩ := hc n hnC θ hθ hthreshold hzero
    have hJell : J ≤ ell := by
      by_contra hnot
      have hsep := phase_cells_ordered ell J (by omega)
        (manuscriptPhaseFn m n θ) (manuscriptPhaseFn m n (root J)) hcell hJroot.2.1
      exact (not_lt_of_ge hphaseOrder) hsep
    have hrootEq : θ = root ell :=
      (hw n hnW ell (hJW.trans hJell) helln).1.unique
        ⟨hθ, hcell, hzero⟩ (hroot ell ⟨hJell, helln⟩)
    refine ⟨ell, ⟨hJell, helln⟩, ?_⟩
    exact hvalue.symm.trans (congrArg (symbol m) hrootEq)
  have hlabels := ordered_tail_index n J hJ1 hnJ (orderedEigenvalue m n) b
    (orderedEigenvalue_monotone m n) hb hocc hcover
  intro j hJj hjn
  have hj := hroot j ⟨hJj, hjn⟩
  refine ⟨root j, hj.1, ?_, hj.2.1, hj.2.2, hrootDeriv j ⟨hJj, hjn⟩⟩
  rw [eigenvalue_in_range (hJ1.trans hJj) hjn]
  exact (hlabels j hJj hjn).symm

#print axioms eigenvalue_eventual_phase_window

end MF21Restart
