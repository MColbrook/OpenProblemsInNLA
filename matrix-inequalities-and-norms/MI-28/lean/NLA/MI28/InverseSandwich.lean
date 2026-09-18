/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

The inverse of a positive congruence is computed with Mathlib's actual matrix
inverse. The CFC inverse bridge follows MI24 SpectralPowers; this local bridge
also allows dimension zero, as required by the frozen C03 auxiliary contract.
-/
import NLA.MI28.Definitions
import NLA.MI24.OrderPowers

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI28

local notation "fpow" => NLA.MI24.spectralPower

lemma power_inverse_sandwich {n : ℕ} (A S : Mat n)
    (hA : A.PosDef) (hS : S.PosDef) :
    fpow (S * A * S) (-1) = fpow S (-1) * fpow A (-1) * fpow S (-1) := by
  have hD := NLA.MI24.posDef_hermitian_sandwich A S hA hS.isHermitian hS.isUnit
  have hinv (X : Mat n) (hX : X.PosDef) : fpow X (-1) = X⁻¹ := by
    -- Ring.inverse and the nonsingular matrix inverse agree in every dimension.
    simpa only [NLA.MI24.spectralPower, CFC.rpow_eq_pow,
      Matrix.nonsing_inv_eq_ringInverse] using
      (CFC.inverse_eq_rpow_neg_one hX.isStrictlyPositive).symm
  rw [hinv _ hD, hinv S hS, hinv A hA, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  simp only [mul_assoc]

end NLA.MI28
