/-
MF-21: the complete original target, stronger smooth-family sharpness,
coefficient uniqueness, and the exact Fourier-matrix correspondence.
Original problem: Barrera, Böttcher, Grudsky and Maximenko.
Original manuscript: George Stepaniants, Department of Computing and
Mathematical Sciences, California Institute of Technology.
Revised formalization: OpenAI Codex AI agents, September 2026.
-/
import MF21.FinalTarget

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace NLA.MF21

theorem full_target : MF21Challenge.FullTarget :=
  MF21Verified.fullTarget

theorem universal_obstruction : MF21Challenge.UniversalObstruction :=
  MF21Verified.universalObstruction

theorem smooth_common_family (m : ℕ) (hm : 3 ≤ m) :
    ∃ d : MF21Challenge.Coefficients,
      (∀ k ≤ 2 * m, ContDiffOn ℝ ∞ (d k) (Icc 0 Real.pi)) ∧
      MF21Challenge.ContinuousCoefficients m d ∧
      (∀ x ∈ Icc 0 Real.pi, d 0 x = MF21Challenge.symbol m x) ∧
      (∀ p : ℕ, p ≤ 2 * m - 1 → MF21Challenge.UniformOrder m p d) ∧
      MF21Challenge.BulkTopOrder m d ∧ ¬ MF21Challenge.UniformOrder m (2 * m) d ∧
      (∃ J : ℕ, 0 < J ∧ ∃ eps : ℝ, 0 < eps ∧
        ∀ᶠ n in atTop, ∃ j : Fin n, j.val < J ∧
          eps / ((n : ℝ) + 2) ^ (2 * m) < |MF21Challenge.remainder m (2 * m) n d j|) ∧
      (∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : Fin n,
        |MF21Challenge.remainder m (2 * m) n d j| ≤ C / ((n : ℝ) + 2) ^ (2 * m)) :=
  MF21Verified.smooth_common_family m hm

theorem fourier_matrix_entries (m n : ℕ) (i j : Fin n) :
    (MF21Challenge.toeplitz m n i j : ℂ) =
      (1 / (2 * Real.pi) : ℂ) *
        ∫ theta in -Real.pi..Real.pi,
          (MF21Challenge.symbol m theta : ℂ) *
            Complex.exp (-(((i.val : ℤ) - j.val) : ℂ) * (theta : ℂ) * Complex.I) :=
  MF21Verified.fourier_matrix_entries m n i j

theorem coefficients_unique (m : ℕ)
    (a b : MF21Challenge.Coefficients)
    (ha : MF21Challenge.ContinuousCoefficients m a)
    (hb : MF21Challenge.ContinuousCoefficients m b)
    (hea : MF21Challenge.BulkTopOrder m a)
    (heb : MF21Challenge.BulkTopOrder m b) :
    ∀ k ≤ 2 * m, ∀ x ∈ Set.Icc 0 Real.pi, a k x = b k x :=
  MF21Uniqueness.mf21_bulk_coefficients_unique m a b ha hb hea heb

end NLA.MF21

#print axioms NLA.MF21.full_target
#print axioms NLA.MF21.universal_obstruction
#print axioms NLA.MF21.smooth_common_family
#print axioms NLA.MF21.fourier_matrix_entries
#print axioms NLA.MF21.coefficients_unique
