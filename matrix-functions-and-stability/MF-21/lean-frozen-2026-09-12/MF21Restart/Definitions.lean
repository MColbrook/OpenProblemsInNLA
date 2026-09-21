import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
Statement-first restart of MF-21. The frozen manuscript is in `original-proof/solution.md`.
No declaration in this file asserts the conjecture. Eigenvalues use one-based published indices.
The real cosine coefficient is the real Fourier representation for this even real symbol;
its equality with the manuscript's complex integral remains a separate obligation.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology

namespace MF21Restart

def symbol (m : ℕ) (θ : ℝ) : ℝ := (2 * Real.sin (θ / 2)) ^ (2 * m)

def fourierCoeff (m : ℕ) (k : ℤ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ θ in -Real.pi..Real.pi,
    symbol m θ * Real.cos ((k : ℝ) * θ)

def toeplitz (m n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => fourierCoeff m ((i.val : ℤ) - (j.val : ℤ))

lemma fourierCoeff_neg (m : ℕ) (k : ℤ) :
    fourierCoeff m (-k) = fourierCoeff m k := by
  simp [fourierCoeff, neg_mul, Real.cos_neg]

lemma toeplitz_isHermitian (m n : ℕ) : (toeplitz m n).IsHermitian := by
  simp only [Matrix.IsHermitian, Matrix.conjTranspose, Matrix.transpose]
  ext i j
  dsimp [toeplitz]
  rw [show (j.val : ℤ) - i.val = -((i.val : ℤ) - j.val) by ring]
  exact fourierCoeff_neg m _

def orderedEigenvalueList (m n : ℕ) : List ℝ :=
  Multiset.sort (Multiset.ofList (List.ofFn (toeplitz_isHermitian m n).eigenvalues))

def orderedEigenvalue (m n : ℕ) (j : Fin n) : ℝ :=
  (orderedEigenvalueList m n).get ⟨j.val, by simp [orderedEigenvalueList]⟩

/-- The manuscript's `λ_{n,j}`, including the largest eigenvalue at `j = n`.
The totalized value 0 outside `1 ≤ j ≤ n` is never used in the target. -/
def eigenvalue (m n j : ℕ) : ℝ :=
  if h : 1 ≤ j ∧ j ≤ n then
    orderedEigenvalue m n ⟨j - 1, by omega⟩
  else 0

lemma eigenvalue_in_range {m n j : ℕ} (h1 : 1 ≤ j) (hn : j ≤ n) :
    eigenvalue m n j = orderedEigenvalue m n ⟨j - 1, by omega⟩ := by
  simp [eigenvalue, h1, hn]

def mesh (n j : ℕ) : ℝ := (j : ℝ) * Real.pi / (n + 2)

def expansion (d : ℕ → ℝ → ℝ) (p n j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (p + 1), d k (mesh n j) / (n + 2 : ℝ) ^ k

def remainder (m : ℕ) (d : ℕ → ℝ → ℝ) (p n j : ℕ) : ℝ :=
  eigenvalue m n j - expansion d p n j

def UniformBound (m : ℕ) (d : ℕ → ℝ → ℝ) (p : ℕ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ n j : ℕ,
    N ≤ n → 1 ≤ j → j ≤ n →
      |remainder m d p n j| ≤ C / (n + 2 : ℝ) ^ (p + 1)

def BulkBound (m : ℕ) (d : ℕ → ℝ → ℝ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ n j : ℕ,
    N ≤ n → 1 ≤ j → Nat.ceil ((Real.log (n + 2 : ℝ)) ^ 2) ≤ j → j ≤ n →
      |remainder m d (2 * m) n j| ≤ C / (n + 2 : ℝ) ^ (2 * m + 1)

/-- All three conclusions use the same coefficient functions, independent of `n,j`.
This is a proposition to be proved, not a theorem or a new assumption. -/
def Target : Prop :=
  ∀ m : ℕ, 3 ≤ m → ∃ d : ℕ → ℝ → ℝ,
    (∀ k ≤ 2 * m, ContinuousOn (d k) (Set.Icc 0 Real.pi)) ∧
    Set.EqOn (d 0) (symbol m) (Set.Icc 0 Real.pi) ∧
    (∀ p ≤ 2 * m - 1, UniformBound m d p) ∧
    BulkBound m d ∧ ¬ UniformBound m d (2 * m)

end MF21Restart
