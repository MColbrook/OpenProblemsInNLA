/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

Concrete determinant identities follow from the unchanged MI24 spectral
power decomposition and Mathlib determinant multiplicativity. Reindexing uses
the actual permutation from the eigenbasis to the decreasing spectrum.
-/
import NLA.MI28.Definitions
import NLA.MI24.CompoundNorm

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section
namespace NLA.MI28

lemma det_unitary_sandwich {n : ℕ} (U : unitary (Mat n)) (X : Mat n) :
    Matrix.det ((U : Mat n) * X * star (U : Mat n)) = Matrix.det X := by
  rw [Matrix.det_mul_comm, ← mul_assoc, Unitary.coe_star_mul_self, one_mul]

lemma det_re_eq_prod_eigenvalues {n : ℕ} (A : Mat n) (hA : A.IsHermitian) :
    A.det.re = ∏ i : Fin n, hA.eigenvalues i := by
  -- The expected type presents RCLike's real coercion as the identical Complex.ofReal.
  have hdet : A.det = ∏ i : Fin n, ((hA.eigenvalues i : ℝ) : ℂ) :=
    hA.det_eq_prod_eigenvalues
  rw [hdet, ← Complex.ofReal_prod, Complex.ofReal_re]

lemma det_spectralPower {n : ℕ} (A : Mat n) (hA : A.PosDef) (r : ℝ) :
    Matrix.det (spectralPower A r) = ((A.det.re ^ r : ℝ) : ℂ) := by
  have hbase : (∏ i : Fin n, hA.isHermitian.eigenvalues i) = A.det.re :=
    (det_re_eq_prod_eigenvalues A hA.isHermitian).symm
  have hdecomp := NLA.MI24.spectralPower_spectral_decomposition A hA.posSemidef r
  -- Match the two transparent CFC-power wrappers and the matrix-star notation.
  change spectralPower A r = _ at hdecomp
  rw [hdecomp, ← Matrix.star_eq_conjTranspose, det_unitary_sandwich, Matrix.det_diagonal,
    ← Complex.ofReal_prod, Real.finsetProd_rpow _ _ (fun i _ => (hA.eigenvalues_pos i).le),
    hbase]

lemma prod_sortedSpectrum_eq_det_re {n : ℕ} (A : Mat n) (hA : A.PosDef) :
    (∏ i : Fin n, sortedSpectrum A hA i) = A.det.re := by
  calc
    _ = ∏ i : Fin n, hA.isHermitian.eigenvalues (NLA.MI24.spectrumIndexEquiv n i) := by
      apply Finset.prod_congr rfl
      intro i _
      exact NLA.MI24.sortedSpectrum_eq_eigenvalues A hA i
    _ = ∏ i : Fin n, hA.isHermitian.eigenvalues i :=
      Equiv.prod_comp (NLA.MI24.spectrumIndexEquiv n) hA.isHermitian.eigenvalues
    _ = A.det.re := (det_re_eq_prod_eigenvalues A hA.isHermitian).symm

lemma det_one_add_eq_prod_sortedSpectrum {n : ℕ} (A : Mat n) (hA : A.PosDef) :
    Matrix.det (1 + A) = ((∏ i : Fin n, (1 + sortedSpectrum A hA i) : ℝ) : ℂ) := by
  let U := hA.isHermitian.eigenvectorUnitary
  let d : Fin n → ℂ := fun i => (hA.isHermitian.eigenvalues i : ℂ)
  have hAeq : A = (U : Mat n) * Matrix.diagonal d * star (U : Mat n) := by
    have hdecomp := NLA.MI24.spectralPower_spectral_decomposition A hA.posSemidef 1
    rw [NLA.MI24.spectralPower_one A hA] at hdecomp
    simpa only [Real.rpow_one, Matrix.star_eq_conjTranspose] using hdecomp
  have hone : (U : Mat n) * (1 : Mat n) * star (U : Mat n) = 1 := by
    rw [mul_one]
    exact U.property.2
  have hadd : 1 + A = (U : Mat n) * (1 + Matrix.diagonal d) * star (U : Mat n) := by
    rw [mul_add, add_mul, hone, ← hAeq]
  have hdiag : (1 : Mat n) + Matrix.diagonal d =
      Matrix.diagonal (fun i => ((1 + hA.isHermitian.eigenvalues i : ℝ) : ℂ)) := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_add]
    congr 1
    funext i
    simp only [Pi.add_apply, Pi.one_apply, d, Complex.ofReal_add, Complex.ofReal_one]
  rw [hadd, det_unitary_sandwich, hdiag, Matrix.det_diagonal, ← Complex.ofReal_prod]
  congr 1
  symm
  calc
    _ = ∏ i : Fin n, (1 + hA.isHermitian.eigenvalues (NLA.MI24.spectrumIndexEquiv n i)) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [show sortedSpectrum A hA i =
        hA.isHermitian.eigenvalues (NLA.MI24.spectrumIndexEquiv n i) from
          NLA.MI24.sortedSpectrum_eq_eigenvalues A hA i]
    _ = _ := Equiv.prod_comp (NLA.MI24.spectrumIndexEquiv n)
      (fun i => 1 + hA.isHermitian.eigenvalues i)

end NLA.MI28
