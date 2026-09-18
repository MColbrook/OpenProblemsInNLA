/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

The unchanged MI24 compound matrices are literal complex minors. Their proved
multiplication and all-real-power identities transport both normalized MI28
matrices to every degree, including degree zero. The modulus bridge uses C02
through the concrete positive Gram sandwich, retaining its C01 dependency.
-/
import NLA.MI28.ModulusPowers
import NLA.MI28.NormalizedPositivity
import NLA.MI24.CompoundSpectral

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI28

open NLA.MI24 (compoundMatrix compoundMatrix_mul compoundMatrix_posDef
  compoundMatrix_spectralPower spectralPower_posDef posDef_hermitian_sandwich)

lemma product_modulus_eq_sandwich_half {n : ℕ} (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) :
    matrixModulus (A * B) = spectralPower (B * spectralPower A 2 * B) (1 / 2) := by
  have hM := matrixModulus_posDef (A * B) (hA.isUnit.mul hB.isUnit)
  have hone : spectralPower (matrixModulus (A * B)) 1 = matrixModulus (A * B) :=
    NLA.MI24.spectralPower_one _ hM
  simpa only [hone] using product_modulus_power A B hA hB 1 (by norm_num)

lemma compound_product_modulus {n : ℕ} (j : ℕ) (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) :
    compoundMatrix j (matrixModulus (A * B)) =
      matrixModulus (compoundMatrix j A * compoundMatrix j B) := by
  -- Use the reused power interface also inside the positivity witness.
  have hG : (B * NLA.MI24.spectralPower A 2 * B).PosDef :=
    posDef_hermitian_sandwich _ B (spectralPower_posDef A hA _) hB.isHermitian hB.isUnit
  rw [product_modulus_eq_sandwich_half A B hA hB,
    product_modulus_eq_sandwich_half _ _ (compoundMatrix_posDef j A hA)
      (compoundMatrix_posDef j B hB)]
  -- Both namespace wrappers are definitionally the same CFC power.
  simpa only [spectralPower, NLA.MI24.spectralPower] using
    (show compoundMatrix j (NLA.MI24.spectralPower (B * NLA.MI24.spectralPower A 2 * B) (1 / 2)) =
      NLA.MI24.spectralPower (compoundMatrix j B *
        NLA.MI24.spectralPower (compoundMatrix j A) 2 * compoundMatrix j B) (1 / 2) by
      rw [compoundMatrix_spectralPower j _ hG, compoundMatrix_mul, compoundMatrix_mul,
        compoundMatrix_spectralPower j A hA])

lemma compound_normalizedH {n : ℕ} (j : ℕ) (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (k p : ℝ) :
    compoundMatrix j (normalizedH A B k p) =
      normalizedH (compoundMatrix j A) (compoundMatrix j B) k p := by
  unfold normalizedH
  -- Expose the identical MI24 power interface for its unchanged compound theorem.
  change compoundMatrix j (NLA.MI24.spectralPower A ((p - k) / 2) *
    NLA.MI24.spectralPower B p * NLA.MI24.spectralPower A ((p - k) / 2)) =
      NLA.MI24.spectralPower (compoundMatrix j A) ((p - k) / 2) *
        NLA.MI24.spectralPower (compoundMatrix j B) p *
          NLA.MI24.spectralPower (compoundMatrix j A) ((p - k) / 2)
  rw [compoundMatrix_mul, compoundMatrix_mul, compoundMatrix_spectralPower j A hA,
    compoundMatrix_spectralPower j B hB]

lemma compound_normalizedZ {n : ℕ} (j : ℕ) (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (k p : ℝ) :
    compoundMatrix j (normalizedZ A B k p) =
      normalizedZ (compoundMatrix j A) (compoundMatrix j B) k p := by
  have hM := matrixModulus_posDef (A * B) (hA.isUnit.mul hB.isUnit)
  unfold normalizedZ
  -- The modulus remains the genuine absolute value of the ordered product.
  change compoundMatrix j (NLA.MI24.spectralPower A (-k / 2) *
    NLA.MI24.spectralPower (matrixModulus (A * B)) p * NLA.MI24.spectralPower A (-k / 2)) =
      NLA.MI24.spectralPower (compoundMatrix j A) (-k / 2) *
        NLA.MI24.spectralPower (matrixModulus (compoundMatrix j A * compoundMatrix j B)) p *
          NLA.MI24.spectralPower (compoundMatrix j A) (-k / 2)
  rw [compoundMatrix_mul, compoundMatrix_mul, compoundMatrix_spectralPower j A hA,
    compoundMatrix_spectralPower j _ hM, compound_product_modulus j A B hA hB]

end NLA.MI28
