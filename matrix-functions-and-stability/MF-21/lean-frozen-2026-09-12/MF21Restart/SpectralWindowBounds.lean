import MF21Restart.DeterminantRemainder
import MF21Restart.Numerics

set_option autoImplicit false
noncomputable section

namespace MF21Restart

private theorem exists_positive_exp_threshold (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ L : ℝ, 0 < L ∧ C * Real.exp (-c * L) < 1 / 8 := by
  let L := max 0 (Real.log (8 * C) / c) + 1
  have hL : 0 < L := by dsimp [L]; linarith [le_max_left 0 (Real.log (8 * C) / c)]
  have hlog : Real.log (8 * C) < c * L := by
    have hh : Real.log (8 * C) / c < L := by
      dsimp [L]
      linarith [le_max_right 0 (Real.log (8 * C) / c)]
    have hx := (div_lt_iff₀ hc).mp hh
    nlinarith only [hx]
  have he : Real.exp (-c * L) < (8 * C)⁻¹ := by
    rw [← Real.exp_log (show 0 < 8 * C by positivity), ← Real.exp_neg]
    apply Real.exp_lt_exp.mpr
    linarith
  refine ⟨L, hL, ?_⟩
  calc
    C * Real.exp (-c * L) < C * (8 * C)⁻¹ := mul_lt_mul_of_pos_left he hC
    _ = 1 / 8 := by field_simp

/-- The actual remainder is small throughout every sufficiently high phase
range, with the same threshold for all matrix sizes. -/
theorem manuscriptError_high_phase_small (m : ℕ) (hm : 2 ≤ m) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ n : ℕ, ∀ θ : ℝ,
      0 ≤ θ → θ ≤ Real.pi →
      (J : ℝ) * Real.pi - Real.pi / 4 ≤ manuscriptPhaseFn m n θ →
      |manuscriptError m n hm θ| < 1 / 4 ∧
        |deriv (manuscriptError m n hm) θ| < (n + 2 : ℝ) / 8 := by
  obtain ⟨c, C, hc, hC, he⟩ := manuscriptError_exp_bounds m hm
  obtain ⟨B, hB, heta⟩ := manuscriptEta_bounded_with_derivative m (by omega)
  obtain ⟨L, hL, hsmall⟩ := exists_positive_exp_threshold c C hc hC
  obtain ⟨J, hJ⟩ := exists_nat_gt (max 1 ((L + B + 9 * Real.pi / 4) / Real.pi))
  have hJ1r : (1 : ℝ) < J := (le_max_left _ _).trans_lt hJ
  have hJ1 : 1 ≤ J := by exact_mod_cast hJ1r.le
  have hJL : L + B + 9 * Real.pi / 4 < (J : ℝ) * Real.pi :=
    (div_lt_iff₀ Real.pi_pos).mp ((le_max_right _ _).trans_lt hJ)
  refine ⟨J, hJ1, ?_⟩
  intro n θ hθ hθπ hphase
  have hetaLower := (abs_le.mp (heta θ ⟨hθ, hθπ⟩).1).1
  have hnt : L ≤ (n : ℝ) * θ := by
    unfold manuscriptPhaseFn at hphase
    nlinarith only [hphase, hetaLower, hθπ, hJL]
  have hexp : Real.exp (-c * (n : ℝ) * θ) ≤ Real.exp (-c * L) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonpos_left hnt (neg_nonpos.mpr hc.le)
    nlinarith only [hmul]
  have hsmall' : C * Real.exp (-c * (n : ℝ) * θ) < 1 / 8 :=
    (mul_le_mul_of_nonneg_left hexp hC.le).trans_lt hsmall
  have hb := he n θ hθ hθπ
  constructor
  · linarith [hb.1]
  · have hn : (0 : ℝ) < n + 1 := by positivity
    calc
      |deriv (manuscriptError m n hm) θ| ≤
          C * (n + 1 : ℝ) * Real.exp (-c * (n : ℝ) * θ) := hb.2
      _ = (C * Real.exp (-c * (n : ℝ) * θ)) * (n + 1 : ℝ) := by ring
      _ < (1 / 8 : ℝ) * (n + 1 : ℝ) := mul_lt_mul_of_pos_right hsmall' hn
      _ < (n + 2 : ℝ) / 8 := by linarith

#print axioms manuscriptError_high_phase_small

end MF21Restart
