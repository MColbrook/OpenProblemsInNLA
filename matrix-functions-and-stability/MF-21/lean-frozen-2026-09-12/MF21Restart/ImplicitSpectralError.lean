import MF21Restart.CoefficientVanishing
import MF21Restart.PhaseQuantitative
import MF21Restart.SymbolDerivative

/-!
Identification of the exact phase preimage with the same constructed Y,
and the actual symbol error (25), retaining its exponential factor.
The statement lock is `IMPLICIT_SPECTRAL_ERROR_STATEMENTS.md`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

/-- The exact phase equation is the actual implicit equation at the
published mesh. Proved interval uniqueness identifies its solution. -/
theorem phase_preimage_eq_implicit
    (m n j : ℕ) (Y : ℝ × ℝ → ℝ) (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε)
    (huniq : ∀ p ∈ Set.Ioo (-r / 2) (Real.pi + r / 2) ×ˢ Set.Ioo (-ε) ε,
      ∀ y ∈ Set.Icc (-r) (Real.pi + r),
        y = p.1 + p.2 * manuscriptEta m y → y = Y p)
    (hjn : j ≤ n) (hstep : 1 / (n + 2 : ℝ) < ε)
    (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) Real.pi)
    (hphase : manuscriptPhaseFn m n y = (j : ℝ) * Real.pi) :
    y = Y (mesh n j, 1 / (n + 2 : ℝ)) := by
  have hden : 0 < (n + 2 : ℝ) := by positivity
  have hstepPos : 0 < 1 / (n + 2 : ℝ) := one_div_pos.mpr hden
  have hx0 : 0 ≤ mesh n j := div_nonneg
    (mul_nonneg (Nat.cast_nonneg j) Real.pi_pos.le) hden.le
  have hxπ : mesh n j ≤ Real.pi := by
    apply (div_le_iff₀ hden).mpr
    have hjnr : (j : ℝ) ≤ n := by exact_mod_cast hjn
    nlinarith [Real.pi_pos]
  have hp : (mesh n j, 1 / (n + 2 : ℝ)) ∈
      Set.Ioo (-r / 2) (Real.pi + r / 2) ×ˢ Set.Ioo (-ε) ε := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, hstep⟩⟩ <;> linarith
  apply huniq _ hp y (by constructor <;> linarith [hy.1, hy.2])
  change y = mesh n j + (1 / (n + 2 : ℝ)) * manuscriptEta m y
  change (n + 2 : ℝ) * y - manuscriptEta m y = (j : ℝ) * Real.pi at hphase
  calc
    y = ((j : ℝ) * Real.pi + manuscriptEta m y) / (n + 2 : ℝ) := by
      apply (eq_div_iff hden.ne').mpr
      nlinarith only [hphase]
    _ = mesh n j + (1 / (n + 2 : ℝ)) * manuscriptEta m y := by
      unfold mesh
      rw [add_div]
      ring

/-- The actual tail eigenvalues have the exponentially small error (25)
for any fixed Y carrying the already proved uniform uniqueness property. -/
theorem eigenvalue_implicit_phase_error_of_unique
    (m : ℕ) (hm : 2 ≤ m) (Y : ℝ × ℝ → ℝ)
    (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε)
    (huniq : ∀ p ∈ Set.Ioo (-r / 2) (Real.pi + r / 2) ×ˢ Set.Ioo (-ε) ε,
      ∀ y ∈ Set.Icc (-r) (Real.pi + r),
        y = p.1 + p.2 * manuscriptEta m y → y = Y p) :
    ∃ (N J : ℕ) (C c : ℝ), 1 ≤ N ∧ 1 ≤ J ∧ 0 < C ∧ 0 < c ∧
      ∀ n : ℕ, N ≤ n → ∀ j : ℕ, J ≤ j → j ≤ n →
        ∃ θ : ℝ, θ ∈ Set.Ioo 0 Real.pi ∧
          Y (mesh n j, 1 / (n + 2 : ℝ)) ∈ Set.Ioo 0 Real.pi ∧
          symbol m θ = eigenvalue m n j ∧
          |θ - Y (mesh n j, 1 / (n + 2 : ℝ))| ≤
            C * Real.exp (-c * (j : ℝ)) / (n + 2 : ℝ) ∧
          θ ≤ C * (j : ℝ) / (n + 2 : ℝ) ∧
          Y (mesh n j, 1 / (n + 2 : ℝ)) ≤ C * (j : ℝ) / (n + 2 : ℝ) ∧
          |eigenvalue m n j - symbol m (Y (mesh n j, 1 / (n + 2 : ℝ)))| ≤
            C * (1 / (n + 2 : ℝ)) ^ (2 * m) * (j : ℝ) ^ (2 * m - 1) *
              Real.exp (-c * (j : ℝ)) := by
  obtain ⟨Nq, J, A, c, hNq, hJ, hA, hc, hq⟩ :=
    eigenvalue_eventual_quantitative_phase_preimage m hm
  obtain ⟨Nε, hNε⟩ := exists_nat_gt (1 / ε)
  let B : ℝ := ((2 * m : ℕ) : ℝ) * A ^ (2 * m)
  let C : ℝ := max A B
  have hAC : A ≤ C := le_max_left _ _
  have hBC : B ≤ C := le_max_right _ _
  have hC : 0 < C := hA.trans_le hAC
  refine ⟨max Nq Nε, J, C, c, hNq.trans (le_max_left _ _), hJ, hC, hc, ?_⟩
  intro n hn j hJj hjn
  have hnq : Nq ≤ n := (le_max_left _ _).trans hn
  have hnε : Nε ≤ n := (le_max_right _ _).trans hn
  have hnεr : (Nε : ℝ) ≤ n := by exact_mod_cast hnε
  have hden : 0 < (n + 2 : ℝ) := by positivity
  have hstepPos : 0 < 1 / (n + 2 : ℝ) := one_div_pos.mpr hden
  have hstep : 1 / (n + 2 : ℝ) < ε := by
    have hlarge : 1 / ε < (n + 2 : ℝ) := by linarith
    have hmul := (div_lt_iff₀ hε).mp hlarge
    apply (div_lt_iff₀ hden).mpr
    nlinarith only [hmul]
  obtain ⟨θ, y, hθ, hy, hvalue, hyphase, hdist, hθsize, hysize⟩ := hq n hnq j hJj hjn
  have hyY : y = Y (mesh n j, 1 / (n + 2 : ℝ)) :=
    phase_preimage_eq_implicit m n j Y r ε hr hε huniq hjn hstep y
      ⟨hy.1.le, hy.2.le⟩ hyphase
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hT : 0 ≤ A * (j : ℝ) / (n + 2 : ℝ) :=
    div_nonneg (mul_nonneg hA.le hj0) hden.le
  have hmean := symbol_difference_le m (A * (j : ℝ) / (n + 2 : ℝ)) θ y
    ⟨hθ.1.le, hθsize⟩ ⟨hy.1.le, hysize⟩
  have hexponent : 2 * m - 1 + 1 = 2 * m := by omega
  have herror : |eigenvalue m n j - symbol m y| ≤
      B * (1 / (n + 2 : ℝ)) ^ (2 * m) * (j : ℝ) ^ (2 * m - 1) *
        Real.exp (-c * (j : ℝ)) := by
    rw [← hvalue]
    calc
      _ ≤ (((2 * m : ℕ) : ℝ) * (A * (j : ℝ) / (n + 2 : ℝ)) ^ (2 * m - 1)) * |θ - y| := hmean
      _ ≤ (((2 * m : ℕ) : ℝ) * (A * (j : ℝ) / (n + 2 : ℝ)) ^ (2 * m - 1)) *
          (A * Real.exp (-c * (j : ℝ)) / (n + 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hdist (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hT _))
      _ = (((2 * m : ℕ) : ℝ) * A ^ (2 * m - 1 + 1)) *
          (1 / (n + 2 : ℝ)) ^ (2 * m - 1 + 1) * (j : ℝ) ^ (2 * m - 1) *
            Real.exp (-c * (j : ℝ)) := by
        simp only [div_eq_mul_inv, mul_pow, pow_succ, one_mul]
        ring
      _ = B * (1 / (n + 2 : ℝ)) ^ (2 * m) * (j : ℝ) ^ (2 * m - 1) *
          Real.exp (-c * (j : ℝ)) := by rw [hexponent]
  have hdistC : |θ - y| ≤ C * Real.exp (-c * (j : ℝ)) / (n + 2 : ℝ) :=
    hdist.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAC (Real.exp_pos _).le) hden.le)
  have hθsizeC : θ ≤ C * (j : ℝ) / (n + 2 : ℝ) :=
    hθsize.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hAC hj0) hden.le)
  have hysizeC : y ≤ C * (j : ℝ) / (n + 2 : ℝ) :=
    hysize.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hAC hj0) hden.le)
  have herrorC : |eigenvalue m n j - symbol m y| ≤
      C * (1 / (n + 2 : ℝ)) ^ (2 * m) * (j : ℝ) ^ (2 * m - 1) *
        Real.exp (-c * (j : ℝ)) :=
    herror.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hBC (pow_nonneg hstepPos.le _))
        (pow_nonneg hj0 _)) (Real.exp_pos _).le)
  refine ⟨θ, hθ, ?_, hvalue, ?_, hθsizeC, ?_, ?_⟩
  · simpa only [hyY] using hy
  · simpa only [hyY] using hdistC
  · simpa only [hyY] using hysizeC
  · simpa only [hyY] using herrorC

#print axioms phase_preimage_eq_implicit
#print axioms eigenvalue_implicit_phase_error_of_unique

end MF21Restart
