/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

The modulus determinant is recovered from C02 and positivity, so the total
products in log-majorization agree exactly. A shared determinant sandwich
identity combines only powers of the same positive matrix, preserving the
noncommuting middle factor in all later determinant factorizations.
-/
import NLA.MI28.SpectrumDeterminant
import NLA.MI28.ModulusPowers
import NLA.MI28.NormalizedPositivity

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI28

lemma det_power_sandwich {n : ℕ} (A X : Mat n) (hA : A.PosDef) (r s : ℝ) :
    Matrix.det (spectralPower A r * X * spectralPower A s) =
      Matrix.det (spectralPower A (r + s)) * Matrix.det X := by
  have hprod : spectralPower A r * spectralPower A s = spectralPower A (r + s) :=
    NLA.MI24.spectralPower_mul A hA r s
  rw [Matrix.det_mul_right_comm, hprod, Matrix.det_mul]

lemma det_product_modulus_re {n : ℕ} (A B : Mat n) (hA : A.PosDef) (hB : B.PosDef) :
    (matrixModulus (A * B)).det.re = A.det.re * B.det.re := by
  have hM := matrixModulus_posDef (A * B) (hA.isUnit.mul hB.isUnit)
  have ha := (Complex.pos_iff.mp hA.det_pos).1
  have hb := (Complex.pos_iff.mp hB.det_pos).1
  have hm := (Complex.pos_iff.mp hM.det_pos).1
  have hbi : B.det.im = 0 := (Complex.pos_iff.mp hB.det_pos).2.symm
  have hdet := congrArg Matrix.det (product_modulus_square A B hA hB)
  rw [det_spectralPower _ hM, Matrix.det_mul, Matrix.det_mul, det_spectralPower A hA] at hdet
  have hre := congrArg Complex.re hdet
  simp only [Complex.ofReal_re, Real.rpow_two, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_im, hbi, mul_zero, zero_mul, add_zero, sub_zero] at hre
  apply (sq_eq_sq₀ hm.le (mul_pos ha hb).le).mp
  nlinarith [hre]

lemma normalized_determinants_eq {n : ℕ} (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (k p : ℝ) :
    Matrix.det (normalizedH A B k p) = Matrix.det (normalizedZ A B k p) := by
  have hM := matrixModulus_posDef (A * B) (hA.isUnit.mul hB.isUnit)
  have ha : 0 < A.det.re := (Complex.pos_iff.mp hA.det_pos).1
  have hb : 0 < B.det.re := (Complex.pos_iff.mp hB.det_pos).1
  have hHexp : (p - k) / 2 + (p - k) / 2 = p - k := by ring
  have hZexp : -k / 2 + -k / 2 = -k := by ring
  have hHdet : Matrix.det (normalizedH A B k p) =
      ((A.det.re ^ (p - k) : ℝ) : ℂ) * ((B.det.re ^ p : ℝ) : ℂ) := by
    rw [normalizedH, det_power_sandwich A _ hA, hHexp,
      det_spectralPower A hA, det_spectralPower B hB]
  have hZdet : Matrix.det (normalizedZ A B k p) =
      ((A.det.re ^ (-k) : ℝ) : ℂ) * (((A.det.re * B.det.re) ^ p : ℝ) : ℂ) := by
    rw [normalizedZ, det_power_sandwich A _ hA, hZexp, det_spectralPower A hA,
      det_spectralPower _ hM, det_product_modulus_re A B hA hB]
  have hscalar : A.det.re ^ (p - k) * B.det.re ^ p =
      A.det.re ^ (-k) * (A.det.re * B.det.re) ^ p := by
    rw [Real.mul_rpow ha.le hb.le, ← mul_assoc, ← Real.rpow_add ha]
    have hexp : p - k = -k + p := by ring
    rw [hexp]
  rw [hHdet, hZdet, ← Complex.ofReal_mul, ← Complex.ofReal_mul, hscalar]

end NLA.MI28
