/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

The modulus of an invertible complex matrix is positive definite because its
Gram matrix is positive definite. Each normalized matrix is then a congruence
of a positive real power by an invertible Hermitian power of A.
All real k and p are allowed, including negative and zero exponents.
-/
import NLA.MI28.Definitions
import NLA.MI24.PolarPowers

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI28

lemma matrixModulus_posDef {n : ℕ} (W : Mat n) (hW : IsUnit W) :
    (matrixModulus W).PosDef := by
  have hG := NLA.MI24.star_mul_self_posDef W hW
  -- Identify the frozen modulus with the CFC half power of its positive Gram matrix.
  simpa only [matrixModulus, CFC.abs, CFC.sqrt_eq_rpow,
    NLA.MI24.spectralPower, CFC.rpow_eq_pow] using
    NLA.MI24.spectralPower_posDef (star W * W) hG (1 / 2)

/-- C04: both normalized matrices are positive definite congruences. -/
theorem normalized_posdef {n : ℕ} (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (k p : ℝ) :
    (normalizedH A B k p).PosDef ∧ (normalizedZ A B k p).PosDef := by
  have hM : (matrixModulus (A * B)).PosDef :=
    matrixModulus_posDef _ (hA.isUnit.mul hB.isUnit)
  constructor
  · exact NLA.MI24.posDef_hermitian_sandwich _ _
      (NLA.MI24.spectralPower_posDef B hB p)
      (NLA.MI24.spectralPower_isHermitian A hA ((p - k) / 2))
      (NLA.MI24.spectralPower_isUnit A hA ((p - k) / 2))
  · exact NLA.MI24.posDef_hermitian_sandwich _ _
      (NLA.MI24.spectralPower_posDef _ hM p)
      (NLA.MI24.spectralPower_isHermitian A hA (-k / 2))
      (NLA.MI24.spectralPower_isUnit A hA (-k / 2))

end NLA.MI28
