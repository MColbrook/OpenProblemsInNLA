/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

The CFC half-power composition route follows the concrete Gram/modulus method
in MI24 FiniteSemantics, authored by George Stepaniants with Codex agent
/root/nm04_final_referee1. Here the actual half-exponent domain proof comes
from frozen MI28 C01. C02 is then reused in the general nonnegative-power
bridge, preserving both the selected theorem and its kernel-certificate path.
No positivity of a non-Hermitian product is assumed.
-/
import NLA.MI28.Numerical

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section
namespace NLA.MI28

/-- The exact complex Gram product; positive semidefinite A and Hermitian B suffice. -/
lemma product_gram {n : ℕ} (A B : Mat n)
    (hA : A.PosSemidef) (hB : B.IsHermitian) :
    (A * B)ᴴ * (A * B) = B * spectralPower A 2 * B := by
  have hA2 : spectralPower A 2 = A * A := by
    simpa [spectralPower, CFC.rpow_eq_pow, pow_two] using CFC.rpow_natCast A 2 hA.nonneg
  -- Convert the matrix conjugate transpose to star before using the star-ring API.
  rw [hA2, ← Matrix.star_eq_conjTranspose, star_mul,
    hB.star_eq, hA.isHermitian.star_eq]
  simp only [mul_assoc]

/-- C02: the certified half is the domain witness in the concrete modulus square. -/
theorem product_modulus_square {n : ℕ} (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) :
    spectralPower (matrixModulus (A * B)) 2 = B * spectralPower A 2 * B := by
  let G := (A * B)ᴴ * (A * B)
  have hG : 0 ≤ G := (Matrix.posSemidef_conjTranspose_mul_self (A * B)).nonneg
  have hmod : matrixModulus (A * B) = spectralPower G (1 / 2) := by
    -- Both sides denote the CFC square root of the same concrete Gram matrix.
    simp only [matrixModulus, spectralPower, CFC.abs, CFC.sqrt_eq_rpow, CFC.rpow_eq_pow,
      Matrix.star_eq_conjTranspose, G]
  have hhalf : 0 ≤ (1 / 2 : ℝ) := half_exponent_interval.1.le
  have hcompose := CFC.rpow_rpow_of_exponent_nonneg G (1 / 2 : ℝ) 2 hhalf
    (by norm_num) hG
  have hhalfTwo : (1 / 2 : ℝ) * 2 = 1 := by ring
  have hsquare : spectralPower (spectralPower G (1 / 2)) 2 = G := by
    simpa only [spectralPower, CFC.rpow_eq_pow, hhalfTwo, CFC.rpow_one G hG]
      using hcompose
  rw [hmod, hsquare]
  exact product_gram A B hA.posSemidef hB.isHermitian

/-- Every nonnegative real modulus power is the matching Gram-sandwich power.
This bridge consumes selected C02, including its substantive C01 dependency. -/
lemma product_modulus_power {n : ℕ} (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (p : ℝ) (hp : 0 ≤ p) :
    spectralPower (matrixModulus (A * B)) p =
      spectralPower (B * spectralPower A 2 * B) (p / 2) := by
  have hpHalf : 0 ≤ p / 2 := by linarith
  have hcompose := CFC.rpow_rpow_of_exponent_nonneg (CFC.abs (A * B))
    (2 : ℝ) (p / 2) (by norm_num) hpHalf (CFC.abs_nonneg (A * B))
  have htwoHalf : (2 : ℝ) * (p / 2) = p := by ring
  have hpower : spectralPower (spectralPower (matrixModulus (A * B)) 2) (p / 2) =
      spectralPower (matrixModulus (A * B)) p := by
    simpa only [spectralPower, matrixModulus, CFC.rpow_eq_pow, htwoHalf] using hcompose
  rw [← hpower, product_modulus_square A B hA hB]

#print axioms product_modulus_square
#assert_trust kernel product_modulus_square

end NLA.MI28
