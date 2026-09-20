import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Nat.Dist
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-!
TRUSTED MATHEMATICAL DEFINITIONS FOR MF-21.

The matrix is given by its explicit real, symmetric signed-binomial entries.
Its identification with the Fourier-defined Toeplitz matrix in the source is
proved separately in FourierCoefficients.lean. The only proof in this file establishes
symmetry so that mathlib's actual Hermitian eigenvalues can be used.

`FullTarget` is a proposition definition, not a theorem asserting that it holds.
`UniversalObstruction` is a separate stronger claim, not silently substituted
for the original same-family obstruction.
-/

noncomputable section

namespace MF21Challenge

/-- The source symbol, exactly (2 sin(theta/2))^(2m). -/
def symbol (m : ℕ) (theta : ℝ) : ℝ :=
  (2 * Real.sin (theta / 2)) ^ (2 * m)

/-- Signed-binomial candidate for the Fourier coefficient at distance d.
`Nat.choose` is zero for d > m; there is no periodic wraparound. -/
def coefficient (m d : ℕ) : ℝ :=
  (-1 : ℝ) ^ d * ((2 * m).choose (m + d) : ℝ)

/-- The n-by-n real Toeplitz matrix with zero-based matrix indices.
Formal equality to the source's Fourier integral is proved in FourierCoefficients.lean. -/
def toeplitz (m n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ coefficient m (Nat.dist i.val j.val)

/-- Elementary symmetry needed to invoke the actual spectral theorem. -/
theorem toeplitz_isHermitian (m n : ℕ) : (toeplitz m n).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  ext i j
  simp [toeplitz, Matrix.transpose_apply, Nat.dist_comm]

/-- Increasing eigenvalues, with multiplicity. Mathlib's `eigenvalues₀` is
antitone, so `Fin.rev` reverses its order. Index j here means source index j+1. -/
def eigenvalue (m n : ℕ) (j : Fin n) : ℝ :=
  (toeplitz_isHermitian m n).eigenvalues₀
    (Fin.cast (Fintype.card_fin n).symm j.rev)

/-- The exact source grid: source index j+1, spacing pi/(n+2). -/
def grid (n : ℕ) (j : Fin n) : ℝ :=
  ((j.val + 1 : ℕ) : ℝ) * Real.pi / ((n : ℝ) + 2)

/-- Natural-log-squared index cutoff, rounded up to a natural number. -/
def cutoff (n : ℕ) : ℕ :=
  Nat.ceil ((Real.log ((n : ℝ) + 2)) ^ 2)

/-- Families are independent of matrix dimension and eigenvalue index.
Only entries 0 through 2m are relevant to the target. -/
abbrev Coefficients := ℕ → ℝ → ℝ

def ContinuousCoefficients (m : ℕ) (d : Coefficients) : Prop :=
  ∀ k ≤ 2 * m, ContinuousOn (d k) (Set.Icc 0 Real.pi)

def remainder (m p n : ℕ) (d : Coefficients) (j : Fin n) : ℝ :=
  eigenvalue m n j -
    ∑ k ∈ Finset.range (p + 1), d k (grid n j) / ((n : ℝ) + 2) ^ k

/-- Constants may depend on m,p,d, but not on n or j. -/
def UniformOrder (m p : ℕ) (d : Coefficients) : Prop :=
  ∃ D : ℝ, 0 < D ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : Fin n,
    |remainder m p n d j| ≤ D / ((n : ℝ) + 2) ^ (p + 1)

/-- The order 2m estimate holds only at or above the source cutoff. -/
def BulkTopOrder (m : ℕ) (d : Coefficients) : Prop :=
  ∃ D : ℝ, 0 < D ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : Fin n,
    cutoff n ≤ j.val + 1 →
    |remainder m (2 * m) n d j| ≤ D / ((n : ℝ) + 2) ^ (2 * m + 1)

/-- All three original assertions use one continuous coefficient family.
The leading coefficient agrees with the symbol on the entire closed interval. -/
def TargetAt (m : ℕ) : Prop :=
  ∃ d : Coefficients, ContinuousCoefficients m d ∧
    (∀ x ∈ Set.Icc 0 Real.pi, d 0 x = symbol m x) ∧
    (∀ p : ℕ, p ≤ 2 * m - 1 → UniformOrder m p d) ∧
    BulkTopOrder m d ∧ ¬ UniformOrder m (2 * m) d

/-- The complete all-m statement. -/
def FullTarget : Prop :=
  ∀ m : ℕ, 3 ≤ m → TargetAt m

/-- Separate stronger statement discussed in the audit: no continuous family
can give an all-index order-2m expansion. Leading coefficient equality is not
assumed here. -/
def UniversalObstruction : Prop :=
  ∀ m : ℕ, 3 ≤ m → ∀ d : Coefficients,
    ContinuousCoefficients m d → ¬ UniformOrder m (2 * m) d

end MF21Challenge
