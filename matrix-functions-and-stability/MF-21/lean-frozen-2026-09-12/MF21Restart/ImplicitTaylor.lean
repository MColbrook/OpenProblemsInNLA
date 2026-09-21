import MF21Restart.Definitions
import MF21Restart.ImplicitPhase
import MF21Restart.ParametricTaylor

/-!
One exact coefficient family (5) for the actual implicit equation (4),
with analytic coefficient functions and the uniform all-order Taylor
remainder (23). The vanishing estimates (24) and the spectral comparison
are separate obligations. See `IMPLICIT_TAYLOR_STATEMENTS.md`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

def implicitPhaseCoefficient (m : ℕ) (Y : ℝ × ℝ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  iteratedDeriv k (fun h : ℝ => symbol m (Y (x, h))) 0 / (k.factorial : ℝ)

/-- The constructed actual phase admits all Taylor orders with one
derivative-defined coefficient family and one uniform h-neighborhood. -/
theorem manuscript_uniform_implicit_taylor (m : ℕ) (hm : 1 ≤ m) :
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
            Cp * |h| ^ (p + 1)) := by
  obtain ⟨r, ε, C, hr, hε, hC, Y, hYreg, hYeq, hYzero, hYuniq⟩ :=
    manuscriptEta_uniform_implicit_phase m hm
  let F : ℝ × ℝ → ℝ := fun p => symbol m (Y p)
  have hg : ContDiff ℝ ⊤ (symbol m) := by
    unfold symbol
    fun_prop
  have hF : ∀ p ∈ Set.Ioo (-r / 2) (Real.pi + r / 2) ×ˢ Set.Ioo (-ε) ε,
      ContDiffAt ℝ ⊤ F p := by
    intro p hp
    exact hg.contDiffAt.comp p (hYreg p hp)
  obtain ⟨δ, hδ, hδε, hrem⟩ :=
    parametricTaylor_uniform_remainder F Real.pi r ε Real.pi_pos.le hr hε hF
  refine ⟨r, ε, C, δ, hr, hε, hC, hδ, hδε, Y,
    hYreg, hYeq, hYzero, hYuniq, ?_, ?_, ?_⟩
  · intro k x hx
    exact parametricTaylorCoefficient_contDiffAt F k x
      (hF (x, 0) ⟨hx, by constructor <;> linarith⟩)
  · intro x hx
    simp only [implicitPhaseCoefficient, iteratedDeriv_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, hYzero x hx]
  · simpa only [F, parametricTaylorCoefficient, implicitPhaseCoefficient] using hrem

#print axioms manuscript_uniform_implicit_taylor

end MF21Restart
