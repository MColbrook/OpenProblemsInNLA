import MF21Restart

/-! Proofs of the full-target, manuscript smoothness, and component
Comparator contracts. Actual execution status is recorded in VERIFICATION.md. -/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology ContDiff
namespace MF21Restart.Contracts

theorem complex_fourier_eq_cosine (m : ℕ) (k : ℤ) :
    (1 / (2 * (Real.pi : ℂ))) *
      (∫ θ in -Real.pi..Real.pi,
        (symbol m θ : ℂ) * Complex.exp (-Complex.I * (k : ℂ) * (θ : ℂ))) =
      (fourierCoeff m k : ℂ) := by
  exact MF21Restart.complex_fourier_eq_cosine m k

theorem bulk_cutoff_pos (n : ℕ) :
    1 ≤ Nat.ceil ((Real.log (n + 2 : ℝ)) ^ 2) := by
  exact MF21Restart.bulk_cutoff_pos n

theorem critical_bound_implies_fixed_index_limit
    (m j : ℕ) {d : ℕ → ℝ → ℝ} {y : ℕ → ℝ} {η : ℝ → ℝ} {B : ℝ}
    (hj : 1 ≤ j)
    (hU : UniformBound m d (2 * m))
    (hTaylor : ∀ᶠ n in atTop,
      |symbol m (y n) - expansion d (2 * m) n j| ≤
        B / (n + 2 : ℝ) ^ (2 * m + 1))
    (hy : Tendsto y atTop (𝓝 0))
    (hη : ContinuousAt η 0)
    (heq : ∀ᶠ n in atTop,
      y n = (Real.pi * j) * (1 / (n + 2 : ℝ)) +
        (1 / (n + 2 : ℝ)) * η (y n)) :
    Tendsto (fun n : ℕ => (n + 2 : ℝ) ^ (2 * m) * eigenvalue m n j)
      atTop (𝓝 ((Real.pi * j + η 0) ^ (2 * m))) := by
  exact MF21Restart.critical_bound_implies_fixed_index_limit m j hj hU hTaylor hy hη heq

theorem exists_log_sq_bulk_scale_gain
    (c : ℝ) (hc : 0 < c) (q : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ,
      Nat.ceil ((Real.log (n + 2 : ℝ)) ^ 2) ≤ j →
      (n + 2 : ℝ) * (j : ℝ) ^ q *
        Real.exp (-c * (j : ℝ)) ≤ 1 := by
  exact MF21Restart.exists_log_sq_bulk_scale_gain c hc q

theorem phase_window_margin : (1 / 4 : ℝ) < Real.sin (Real.pi / 4) := by
  exact MF21Restart.phase_window_margin

theorem manuscript_smooth_target :
    ∀ m : ℕ, 3 ≤ m → ∃ d : ℕ → ℝ → ℝ,
      (∀ k ≤ 2 * m, ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, ContDiffAt ℝ ∞ (d k) x) ∧
      Set.EqOn (d 0) (symbol m) (Set.Icc 0 Real.pi) ∧
      (∀ p ≤ 2 * m - 1, UniformBound m d p) ∧
      BulkBound m d ∧ ¬UniformBound m d (2 * m) := by
  exact MF21Restart.manuscript_smooth_target

theorem target_proved : Target := by
  exact MF21Restart.target_proved

end MF21Restart.Contracts
