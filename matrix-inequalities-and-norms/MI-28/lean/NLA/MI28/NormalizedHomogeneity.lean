/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

The unchanged MI24 PowerScaling theorem supplies every real CFC exponent.
Mathlib supplies scalar homogeneity of the genuine complex modulus. Scalar
tower conversion is explicit because the frozen contract uses complex scalars,
while the reused power theorem returns real scalar multiplication.
-/
import NLA.MI28.Definitions
import NLA.MI24.PowerScaling

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI28

/-- C13: the exact positive scalar factor for both normalized matrices. -/
theorem normalized_homogeneity {n : ℕ} (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (k p c : ℝ) (hc : 0 < c) :
    normalizedH A ((c : ℂ) • B) k p = (Real.rpow c p : ℂ) • normalizedH A B k p ∧
    normalizedZ A ((c : ℂ) • B) k p = (Real.rpow c p : ℂ) • normalizedZ A B k p := by
  clear hA
  have hreal (r : ℝ) (X : Mat n) : r • X = (r : ℂ) • X := by
    ext i j
    -- Matrix scalar multiplication is entrywise; use the concrete complex scalar bridge.
    change r • X i j = (r : ℂ) * X i j
    exact Complex.real_smul
  have hscale (X : Mat n) (hX : X.PosSemidef) :
      spectralPower ((c : ℂ) • X) p = (Real.rpow c p : ℂ) • spectralPower X p := by
    calc
      _ = (c ^ p : ℝ) • spectralPower X p :=
        NLA.MI24.spectralPower_smul_nonneg X hX c hc.le p
      _ = (Real.rpow c p : ℂ) • spectralPower X p := by
        simpa only [Real.rpow_eq_pow] using hreal (Real.rpow c p) (spectralPower X p)
  have hmod : matrixModulus (A * ((c : ℂ) • B)) =
      (c : ℂ) • matrixModulus (A * B) := by
    rw [mul_smul_comm]
    calc
      _ = c • matrixModulus (A * B) := by
        simp only [matrixModulus, CFC.abs_smul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hc]
      _ = (c : ℂ) • matrixModulus (A * B) := hreal c _
  have hM : (matrixModulus (A * B)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg (A * B))
  constructor
  · simp only [normalizedH, hscale B hB.posSemidef, mul_smul_comm, smul_mul_assoc]
  · simp only [normalizedZ]
    -- Rewrite the modulus before scalar distribution changes the product A * (c • B).
    rw [hmod, hscale _ hM]
    simp only [mul_smul_comm, smul_mul_assoc]

end NLA.MI28
