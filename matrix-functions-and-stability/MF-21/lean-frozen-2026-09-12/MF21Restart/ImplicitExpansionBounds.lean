import MF21Restart.ExpansionAssembly
import MF21Restart.ImplicitSpectralData

/-! The actual derivative-defined coefficient family has the bulk bound.
The all-index bounds require only the explicit fixed-prefix eigenvalue
estimate until interlacing supplies it. See EXPANSION_ASSEMBLY_STATEMENTS.md. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

/-- Fixed-Y interface: callers can retain all other properties of their
already chosen actual implicit phase. No new Y is selected here. -/
theorem implicitPhase_expansion_bounds_of_data
    (m : ℕ) (hm : 1 ≤ m) (Y : ℝ × ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hTaylor : ∀ p : ℕ, ∃ Cp : ℝ, 0 < Cp ∧
      ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, ∀ h : ℝ, |h| ≤ δ →
        |symbol m (Y (x, h)) -
            ∑ k ∈ Finset.range (p + 1), implicitPhaseCoefficient m Y k x * h ^ k| ≤
          Cp * |h| ^ (p + 1))
    (hvan : ∀ k : ℕ, k ≤ 2 * m → ∃ Ck : ℝ, 0 < Ck ∧
      ∀ x ∈ Set.Icc (0 : ℝ) Real.pi,
        |implicitPhaseCoefficient m Y k x| ≤ Ck * x ^ (2 * m - k))
    (N J : ℕ) (Cs c : ℝ) (hCs : 0 < Cs) (hc : 0 < c)
    (hTail : ∀ n : ℕ, N ≤ n → ∀ j : ℕ, J ≤ j → j ≤ n →
      |eigenvalue m n j - symbol m (Y (mesh n j, 1 / (n + 2 : ℝ)))| ≤
        Cs * (1 / (n + 2 : ℝ)) ^ (2 * m) * (j : ℝ) ^ (2 * m - 1) *
          Real.exp (-c * (j : ℝ))) :
    BulkBound m (implicitPhaseCoefficient m Y) ∧
      ((∀ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
        ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → j < J → j ≤ n →
          |eigenvalue m n j| ≤ C * (1 / (n + 2 : ℝ)) ^ (2 * m)) →
        ∀ p : ℕ, p ≤ 2 * m - 1 → UniformBound m (implicitPhaseCoefficient m Y) p) := by
  refine ⟨bulkBound_of_taylor_spectral_tail m Y (implicitPhaseCoefficient m Y) δ hδ
    hTaylor N J Cs c hCs hc hTail, ?_⟩
  intro hLow p hp
  exact uniformBound_of_taylor_vanishing_spectral_tail m p hm hp Y
    (implicitPhaseCoefficient m Y) δ hδ hTaylor hvan N J Cs c hCs hc hTail hLow

/-- One actually constructed phase and one exact coefficient family.
BulkBound is unconditional; the only remaining premise for the global
orders is the stated finite-prefix spectral estimate. -/
theorem manuscript_implicit_expansion_bounds (m : ℕ) (hm : 2 ≤ m) :
    ∃ Y : ℝ × ℝ → ℝ,
      (∀ k : ℕ, ContinuousOn (implicitPhaseCoefficient m Y k) (Set.Icc 0 Real.pi)) ∧
      Set.EqOn (implicitPhaseCoefficient m Y 0) (symbol m) (Set.Icc 0 Real.pi) ∧
      BulkBound m (implicitPhaseCoefficient m Y) ∧
      ((∀ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
        ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → j < J → j ≤ n →
          |eigenvalue m n j| ≤ C * (1 / (n + 2 : ℝ)) ^ (2 * m)) →
        ∀ p : ℕ, p ≤ 2 * m - 1 → UniformBound m (implicitPhaseCoefficient m Y) p) := by
  obtain ⟨r, ε, C, δ, hr, _hε, _hC, hδ, _hδε, Y,
    _hYreg, _hYeq, _hYzero, _hYuniq, hcoeff, hzero, hTaylor, hvan,
    N, J, Cs, c, _hN, _hJ, hCs, hc, htail⟩ :=
    manuscript_implicit_taylor_with_spectral_error m hm
  have hTail : ∀ n : ℕ, N ≤ n → ∀ j : ℕ, J ≤ j → j ≤ n →
      |eigenvalue m n j - symbol m (Y (mesh n j, 1 / (n + 2 : ℝ)))| ≤
        Cs * (1 / (n + 2 : ℝ)) ^ (2 * m) * (j : ℝ) ^ (2 * m - 1) *
          Real.exp (-c * (j : ℝ)) := by
    intro n hn j hj hjn
    obtain ⟨θ, _hθ, _hy, _hev, _hdist, _hθsize, _hysize, he⟩ := htail n hn j hj hjn
    exact he
  have hbounds := implicitPhase_expansion_bounds_of_data m (by omega) Y δ hδ
    hTaylor hvan N J Cs c hCs hc hTail
  refine ⟨Y, ?_, ?_, hbounds.1, hbounds.2⟩
  · intro k x hx
    apply (hcoeff k x ?_).continuousAt.continuousWithinAt
    constructor <;> linarith [hx.1, hx.2]
  · intro x hx
    apply hzero x
    constructor <;> linarith [hx.1, hx.2]

#print axioms implicitPhase_expansion_bounds_of_data
#print axioms manuscript_implicit_expansion_bounds

end MF21Restart

