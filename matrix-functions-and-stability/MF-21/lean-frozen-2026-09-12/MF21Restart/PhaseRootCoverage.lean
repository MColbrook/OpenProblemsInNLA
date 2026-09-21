import MF21Restart.FinalPhaseWindow
import MF21Restart.SpectralWindowBounds
import Mathlib.Algebra.Order.Floor.Semiring

/-!
Every sufficiently high actual residual zero belongs to one of the
ordinary phase windows with label between J and n. This is the coverage
part of manuscript Lemma 4; it does not identify ordered eigenvalue indices.
The prior statement lock is `PHASE_ROOT_COVERAGE_STATEMENTS.md`.
-/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

private theorem exists_nearest_phase_index (n J : ℕ) (x : ℝ)
    (hlo : (J : ℝ) * Real.pi - Real.pi / 4 ≤ x)
    (hup : x ≤ (n + 1 : ℝ) * Real.pi) :
    ∃ k : ℕ, J ≤ k ∧ k ≤ n + 1 ∧ |x - (k : ℝ) * Real.pi| ≤ Real.pi / 2 := by
  let q : ℝ := x / Real.pi + 1 / 2
  let k : ℕ := Nat.floor q
  have hloq : (J : ℝ) - 1 / 4 ≤ x / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).mpr
    calc
      ((J : ℝ) - 1 / 4) * Real.pi = (J : ℝ) * Real.pi - Real.pi / 4 := by ring
      _ ≤ x := hlo
  have hJq : (J : ℝ) ≤ q := by
    dsimp only [q]
    linarith
  have hq : 0 ≤ q := (Nat.cast_nonneg J).trans hJq
  have hJk : J ≤ k := Nat.le_floor hJq
  have hfl : (k : ℝ) ≤ q := Nat.floor_le hq
  have hfu : q < (k : ℝ) + 1 := Nat.lt_floor_add_one q
  have hupq : x / Real.pi ≤ (n + 1 : ℝ) := (div_le_iff₀ Real.pi_pos).mpr hup
  have hqlt : q < ((n + 2 : ℕ) : ℝ) := by
    change x / Real.pi + 1 / 2 < ((n + 2 : ℕ) : ℝ)
    push_cast
    linarith
  have hklt : k < n + 2 := (Nat.floor_lt hq).mpr hqlt
  have hbelow : (k : ℝ) - 1 / 2 ≤ x / Real.pi := by
    change (k : ℝ) ≤ x / Real.pi + 1 / 2 at hfl
    linarith
  have habove : x / Real.pi ≤ (k : ℝ) + 1 / 2 := by
    change x / Real.pi + 1 / 2 < (k : ℝ) + 1 at hfu
    linarith
  have hloMul := (le_div_iff₀ Real.pi_pos).mp hbelow
  have hupMul := (div_le_iff₀ Real.pi_pos).mp habove
  refine ⟨k, hJk, by omega, abs_le.mpr ⟨?_, ?_⟩⟩ <;>
    nlinarith only [hloMul, hupMul]

/-- On a nearest half-period, a sine smaller than the certified quarter
margin must lie inside the quarter-period window. -/
private theorem phase_distance_small_of_sine_small (x : ℝ) (k : ℕ)
    (hhalf : |x - (k : ℝ) * Real.pi| ≤ Real.pi / 2)
    (hsmall : |Real.sin x| < 1 / 4) :
    |x - (k : ℝ) * Real.pi| ≤ Real.pi / 4 := by
  by_contra hnot
  have hlarge : Real.pi / 4 < |x - (k : ℝ) * Real.pi| := lt_of_not_ge hnot
  have hcompare := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ Real.pi / 4) hhalf hlarge.le
  have habs := Real.abs_sin_eq_sin_abs_of_abs_le_pi
    (hhalf.trans (by linarith [Real.pi_pos] : Real.pi / 2 ≤ Real.pi))
  have hshift : |Real.sin (x - (k : ℝ) * Real.pi)| = |Real.sin x| := by
    rw [Real.sin_sub_nat_mul_pi, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hmargin := phase_window_margin.trans_le hcompare
  rw [← habs, hshift] at hmargin
  exact (not_lt_of_ge hsmall.le) hmargin

theorem manuscriptResidual_high_phase_root_coverage (m : ℕ) (hm : 2 ≤ m) :
    ∃ N J : ℕ, 1 ≤ N ∧ 1 ≤ J ∧
      ∀ n : ℕ, N ≤ n → ∀ θ : ℝ, θ ∈ Set.Ioo 0 Real.pi →
        (J : ℝ) * Real.pi - Real.pi / 4 ≤ manuscriptPhaseFn m n θ →
        manuscriptResidual m n hm θ = 0 →
        ∃ k : ℕ, J ≤ k ∧ k ≤ n ∧
          |manuscriptPhaseFn m n θ - (k : ℝ) * Real.pi| ≤ Real.pi / 4 := by
  obtain ⟨Nmono, hmono⟩ := manuscriptPhaseFn_eventual_strictMonoOn m (by omega)
  obtain ⟨Nfinal, hNfinal, hfinal⟩ := manuscriptFinalPhaseWindow_eventual_nonzero m hm
  obtain ⟨J, hJ, hsmall⟩ := manuscriptError_high_phase_small m hm
  refine ⟨max Nfinal Nmono, J, hNfinal.trans (le_max_left _ _), hJ, ?_⟩
  intro n hn θ hθ hphase hzero
  have hnMono : Nmono ≤ n := (le_max_right _ _).trans hn
  have hnFinal : Nfinal ≤ n := (le_max_left _ _).trans hn
  have hθcc : θ ∈ Set.Icc 0 Real.pi := ⟨hθ.1.le, hθ.2.le⟩
  have hupper := (hmono n hnMono).monotoneOn hθcc
    (show Real.pi ∈ Set.Icc 0 Real.pi from ⟨Real.pi_pos.le, le_rfl⟩) hθ.2.le
  rw [manuscriptPhaseFn_pi m n (by omega)] at hupper
  obtain ⟨k, hJk, hkn, hhalf⟩ :=
    exists_nearest_phase_index n J (manuscriptPhaseFn m n θ) hphase hupper
  have hsine : |Real.sin (manuscriptPhaseFn m n θ)| < 1 / 4 := by
    have herror := (hsmall n θ hθ.1.le hθ.2.le hphase).1
    have heq : Real.sin (manuscriptPhaseFn m n θ) = -manuscriptError m n hm θ := by
      change Real.sin (manuscriptPhaseFn m n θ) + manuscriptError m n hm θ = 0 at hzero
      linarith only [hzero]
    rw [heq, abs_neg]
    exact herror
  have hcell := phase_distance_small_of_sine_small (manuscriptPhaseFn m n θ) k hhalf hsine
  have hne : k ≠ n + 1 := by
    intro heq
    subst k
    have hfinalcell :
        |manuscriptPhaseFn m n θ - (n + 1 : ℝ) * Real.pi| ≤ Real.pi / 4 := by
      simpa only [Nat.cast_add, Nat.cast_one] using hcell
    exact (hfinal n hnFinal θ hθ hfinalcell).2 hzero
  exact ⟨k, hJk, by omega, hcell⟩

#print axioms manuscriptResidual_high_phase_root_coverage

end MF21Restart
