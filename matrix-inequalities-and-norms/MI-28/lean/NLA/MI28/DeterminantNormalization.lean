/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

Explicit ordered factorizations give C18. The right sum need not be Hermitian:
its two outer factors are A^((k+p)/2) and A^((k-p)/2). Their determinants
combine to det(A^k), while the middle factor is exactly I+H. The left sum
uses the positive congruence with A^(k/2). Both follow from one shared identity.
-/
import NLA.MI28.NormalizedDeterminant

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI28

lemma power_factor_one_add {n : ℕ} (A X : Mat n) (hA : A.PosDef) (u v w z : ℝ) :
    spectralPower A u * (1 + spectralPower A w * X * spectralPower A z) * spectralPower A v =
      spectralPower A (u + v) + spectralPower A (u + w) * X * spectralPower A (z + v) := by
  have huv : spectralPower A u * spectralPower A v = spectralPower A (u + v) :=
    NLA.MI24.spectralPower_mul A hA u v
  have huw : spectralPower A u * spectralPower A w = spectralPower A (u + w) :=
    NLA.MI24.spectralPower_mul A hA u w
  have hzv : spectralPower A z * spectralPower A v = spectralPower A (z + v) :=
    NLA.MI24.spectralPower_mul A hA z v
  calc
    _ = spectralPower A u * spectralPower A v +
        (spectralPower A u * spectralPower A w) * X *
          (spectralPower A z * spectralPower A v) := by
      simp only [mul_add, add_mul, mul_one, mul_assoc]
    _ = _ := by rw [huv, huw, hzv]

/-- C18: determinant normalization for both literal sums, including the non-Hermitian right sum. -/
theorem determinant_normalization {n : ℕ} (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (k p : ℝ) :
    determinantRight A B k p =
      Matrix.det (spectralPower A k) * Matrix.det (1 + normalizedH A B k p) ∧
    determinantLeft A B k p =
      Matrix.det (spectralPower A k) * Matrix.det (1 + normalizedZ A B k p) := by
  have hzero : spectralPower A 0 = 1 := NLA.MI24.spectralPower_zero A hA
  have hRsum : (k + p) / 2 + (k - p) / 2 = k := by ring
  have hRleft : (k + p) / 2 + (p - k) / 2 = p := by ring
  have hRright : (p - k) / 2 + (k - p) / 2 = 0 := by ring
  have hR : spectralPower A ((k + p) / 2) * (1 + normalizedH A B k p) *
      spectralPower A ((k - p) / 2) = spectralPower A k + spectralPower A p * spectralPower B p := by
    rw [normalizedH, power_factor_one_add A _ hA, hRsum, hRleft, hRright, hzero, mul_one]
  have hLsum : k / 2 + k / 2 = k := by ring
  have hLleft : k / 2 + -k / 2 = 0 := by ring
  have hLright : -k / 2 + k / 2 = 0 := by ring
  have hL : spectralPower A (k / 2) * (1 + normalizedZ A B k p) * spectralPower A (k / 2) =
      spectralPower A k + spectralPower (matrixModulus (A * B)) p := by
    rw [normalizedZ, power_factor_one_add A _ hA, hLsum, hLleft, hLright, hzero,
      one_mul, mul_one]
  constructor
  · have hdet := congrArg Matrix.det hR
    rw [det_power_sandwich A _ hA, hRsum] at hdet
    exact hdet.symm
  · have hdet := congrArg Matrix.det hL
    rw [det_power_sandwich A _ hA, hLsum] at hdet
    exact hdet.symm

end NLA.MI28
