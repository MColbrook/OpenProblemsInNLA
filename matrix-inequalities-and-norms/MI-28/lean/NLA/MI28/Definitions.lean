/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the eventual project LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted statement preparation by Codex agent /root/nm04_final_referee1.

UNELABORATED STATEMENT DRAFT. No MI28 proof implementation or freeze exists.
Actual CFC, matrix and Euclidean norm definitions follow the MI24 formalization;
the eigenvalue/prefix definitions reproduce its transparent mathematical definitions.
Original problem/prior large-k mathematics: Ghabries, Abbas, Mourad, Assi.
Full remaining analytic solution: George Stepaniants, using Furuta and Loewner-Heinz.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI28

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
def spectralPower {n : ℕ} (A : Mat n) (r : ℝ) : Mat n := CFC.rpow A r
def matrixModulus {n : ℕ} (X : Mat n) : Mat n := CFC.abs X
def operatorNorm {n : ℕ} (X : Mat n) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X‖

def normalizedH {n : ℕ} (A B : Mat n) (k p : ℝ) : Mat n :=
  spectralPower A ((p - k) / 2) * spectralPower B p *
    spectralPower A ((p - k) / 2)

def normalizedZ {n : ℕ} (A B : Mat n) (k p : ℝ) : Mat n :=
  spectralPower A (-k / 2) * spectralPower (matrixModulus (A * B)) p *
    spectralPower A (-k / 2)

def determinantLeft {n : ℕ} (A B : Mat n) (k p : ℝ) : ℂ :=
  Matrix.det (spectralPower A k + spectralPower (matrixModulus (A * B)) p)

def determinantRight {n : ℕ} (A B : Mat n) (k p : ℝ) : ℂ :=
  Matrix.det (spectralPower A k + spectralPower A p * spectralPower B p)

/-- Decreasing, multiplicity-preserving eigenvalues of a genuinely PD matrix. -/
def sortedSpectrum {n : ℕ} (A : Mat n) (hA : A.PosDef) (i : Fin n) : ℝ :=
  hA.isHermitian.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i)

def prefixProduct {n : ℕ} (x : Fin n → ℝ) (j : ℕ) (hj : j ≤ n) : ℝ :=
  ∏ i : Fin j, x (Fin.castLE hj i)

def WeakLogMajorized {n : ℕ} (x y : Fin n → ℝ) : Prop :=
  ∀ j : ℕ, ∀ hj : j ≤ n, prefixProduct x j hj ≤ prefixProduct y j hj

def LogMajorized {n : ℕ} (x y : Fin n → ℝ) : Prop :=
  WeakLogMajorized x y ∧ (∏ i : Fin n, x i) = ∏ i : Fin n, y i

/-- Universal implication; a proved helper, never an assumption of the final theorem. -/
def OrderImplication (k p : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ A B : Mat n, A.PosDef → B.PosDef →
    spectralPower (matrixModulus (A * B)) p ≤ spectralPower A k →
      spectralPower B p ≤ spectralPower A (k - p)

/-- Source Theorem 1, including PD witnesses so that vacuity is impossible. -/
def FullLogMajorization : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ A B : Mat n, A.PosDef → B.PosDef →
    ∀ k p : ℝ, 0 ≤ k → 0 ≤ p → p ≤ 2 →
      ∃ hH : (normalizedH A B k p).PosDef,
      ∃ hZ : (normalizedZ A B k p).PosDef,
        LogMajorized (sortedSpectrum (normalizedH A B k p) hH)
          (sortedSpectrum (normalizedZ A B k p) hZ)

/-- Complete unchanged canonical determinant target. The explicit imaginary-part
equalities give the real-order meaning for the possibly non-Hermitian right sum. -/
def DeterminantComparison : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ A B : Mat n, A.PosDef → B.PosDef →
    ∀ k p : ℝ, 0 ≤ k → 0 ≤ p → p ≤ 2 →
      (determinantLeft A B k p).im = 0 ∧
      (determinantRight A B k p).im = 0 ∧
      (determinantRight A B k p).re ≤ (determinantLeft A B k p).re

end NLA.MI28
