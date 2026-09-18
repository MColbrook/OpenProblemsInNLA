/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

Only the exponent varies. One fixed unitary diagonalization of the positive
matrix reduces continuity to scalar powers of its strictly positive eigenvalues.
The existing Mathlib diagonal-continuity and Euclidean norm bridges are used
directly; no continuity statement for sorted eigenvalues is needed.
-/
import NLA.MI28.Definitions
import NLA.MI24.TraceSpectral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI28

lemma spectralPower_continuous_exponent {n : ℕ} (A : Mat n) (hA : A.PosDef) :
    Continuous (fun r : ℝ => spectralPower A r) := by
  have hdiag : Continuous (fun r : ℝ =>
      Matrix.diagonal (fun i : Fin n => ((hA.isHermitian.eigenvalues i ^ r : ℝ) : ℂ))) := by
    apply Continuous.matrix_diagonal
    apply continuous_pi
    intro i
    exact Complex.continuous_ofReal.comp
      (Real.continuous_const_rpow (ne_of_gt (hA.eigenvalues_pos i)))
  have hdecomp : (fun r : ℝ => spectralPower A r) =
      fun r => (hA.isHermitian.eigenvectorUnitary : Mat n) *
        Matrix.diagonal (fun i => ((hA.isHermitian.eigenvalues i ^ r : ℝ) : ℂ)) *
          (hA.isHermitian.eigenvectorUnitary : Mat n)ᴴ := by
    funext r
    exact NLA.MI24.spectralPower_spectral_decomposition A hA.posSemidef r
  rw [hdecomp]
  exact (continuous_const.mul hdiag).mul continuous_const

/-- C14: continuity in the full real base exponent for the literal normalized matrices. -/
theorem normalized_norm_continuous {n : ℕ} (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (p : ℝ) :
    Continuous (fun k : ℝ => operatorNorm (normalizedH A B k p)) ∧
    Continuous (fun k : ℝ => operatorNorm (normalizedZ A B k p)) := by
  have hpow := spectralPower_continuous_exponent A hA
  have hHpow : Continuous (fun k : ℝ => spectralPower A ((p - k) / 2)) :=
    hpow.comp ((continuous_const.sub continuous_id).div_const 2)
  have hZpow : Continuous (fun k : ℝ => spectralPower A (-k / 2)) :=
    hpow.comp (continuous_id.neg.div_const 2)
  have hH : Continuous (fun k : ℝ => normalizedH A B k p) :=
    (hHpow.mul continuous_const).mul hHpow
  have hZ : Continuous (fun k : ℝ => normalizedZ A B k p) :=
    (hZpow.mul continuous_const).mul hZpow
  constructor
  · -- The scoped L2 norm is the frozen Euclidean continuous-linear-map norm.
    simpa only [operatorNorm, Matrix.l2_opNorm_toEuclideanCLM] using hH.norm
  · simpa only [operatorNorm, Matrix.l2_opNorm_toEuclideanCLM] using hZ.norm

end NLA.MI28
