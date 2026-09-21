import MF21Restart.ImplicitSpectralError

/-!
One constructed Y and one exact derivative-defined coefficient family
carry the implicit equation, all-order uniform Taylor expansion,
coefficient vanishing, and actual exponential tail spectral error.
Low-index estimates, extension independence, and final target assembly
remain separate. See `IMPLICIT_SPECTRAL_ERROR_STATEMENTS.md`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

theorem manuscript_implicit_taylor_with_spectral_error (m : ℕ) (hm : 2 ≤ m) :
    ∃ r ε C δ : ℝ, 0 < r ∧ 0 < ε ∧ 0 < C ∧ 0 < δ ∧ δ < ε ∧
      ∃ Y : ℝ × ℝ → ℝ,
      let D := Set.Ioo (-r / 2) (Real.pi + r / 2) ×ˢ Set.Ioo (-ε) ε
      (∀ p ∈ D, ContDiffAt ℝ ⊤ Y p) ∧
      (∀ p ∈ D, Y p ∈ Set.Ioo (-r) (Real.pi + r) ∧
        Y p = p.1 + p.2 * manuscriptEta m (Y p) ∧
        |Y p - p.1| ≤ C * |p.2|) ∧
      (∀ x ∈ Set.Ioo (-r / 2) (Real.pi + r / 2), Y (x, 0) = x) ∧
      (∀ p ∈ D, ∀ y ∈ Set.Icc (-r) (Real.pi + r),
        y = p.1 + p.2 * manuscriptEta m y → y = Y p) ∧
      (∀ k : ℕ, ∀ x ∈ Set.Ioo (-r / 2) (Real.pi + r / 2),
        ContDiffAt ℝ ⊤ (implicitPhaseCoefficient m Y k) x) ∧
      (∀ x ∈ Set.Ioo (-r / 2) (Real.pi + r / 2),
        implicitPhaseCoefficient m Y 0 x = symbol m x) ∧
      (∀ p : ℕ, ∃ Cp : ℝ, 0 < Cp ∧
        ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, ∀ h : ℝ, |h| ≤ δ →
          |symbol m (Y (x, h)) -
              ∑ k ∈ Finset.range (p + 1), implicitPhaseCoefficient m Y k x * h ^ k| ≤
            Cp * |h| ^ (p + 1)) ∧
      (∀ k : ℕ, k ≤ 2 * m → ∃ Ck : ℝ, 0 < Ck ∧
        ∀ x ∈ Set.Icc (0 : ℝ) Real.pi,
          |implicitPhaseCoefficient m Y k x| ≤ Ck * x ^ (2 * m - k)) ∧
      (∃ (N J : ℕ) (Cs c : ℝ), 1 ≤ N ∧ 1 ≤ J ∧ 0 < Cs ∧ 0 < c ∧
        ∀ n : ℕ, N ≤ n → ∀ j : ℕ, J ≤ j → j ≤ n →
          ∃ θ : ℝ, θ ∈ Set.Ioo 0 Real.pi ∧
            Y (mesh n j, 1 / (n + 2 : ℝ)) ∈ Set.Ioo 0 Real.pi ∧
            symbol m θ = eigenvalue m n j ∧
            |θ - Y (mesh n j, 1 / (n + 2 : ℝ))| ≤
              Cs * Real.exp (-c * (j : ℝ)) / (n + 2 : ℝ) ∧
            θ ≤ Cs * (j : ℝ) / (n + 2 : ℝ) ∧
            Y (mesh n j, 1 / (n + 2 : ℝ)) ≤ Cs * (j : ℝ) / (n + 2 : ℝ) ∧
            |eigenvalue m n j - symbol m (Y (mesh n j, 1 / (n + 2 : ℝ)))| ≤
              Cs * (1 / (n + 2 : ℝ)) ^ (2 * m) * (j : ℝ) ^ (2 * m - 1) *
                Real.exp (-c * (j : ℝ))) := by
  obtain ⟨r, ε, C, δ, hr, hε, hC, hδ, hδε, Y,
    hYreg, hYeq, hYzero, hYuniq, hcoeff, hzeroCoeff, hrem, hvan⟩ :=
    manuscript_uniform_implicit_taylor_with_vanishing m (by omega)
  exact ⟨r, ε, C, δ, hr, hε, hC, hδ, hδε, Y,
    hYreg, hYeq, hYzero, hYuniq, hcoeff, hzeroCoeff, hrem, hvan,
    eigenvalue_implicit_phase_error_of_unique m hm Y r ε hr hε hYuniq⟩

#print axioms manuscript_implicit_taylor_with_spectral_error

end MF21Restart
