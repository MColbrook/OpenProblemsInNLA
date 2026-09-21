import MF21Restart.CirculantEmbedding
import MF21Restart.FourierLaurent
import MF21Restart.CharacteristicRoots
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
The complete characteristic polynomial of the actual Fourier circulant.
Geometric Fourier vectors give an explicit Vandermonde diagonalization;
the nonzero Vandermonde determinant accounts for all multiplicities.
See the prior lock `CIRCULANT_SPECTRUM_STATEMENTS.md`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

theorem periodicFourierColumn_laurent_sum (m N : ℕ) (hmN : m < N)
    (z : ℂ) (hz : z ≠ 0) (hzN : z ^ N = 1) :
    (∑ k : Fin N, (periodicFourierColumn m N k : ℂ) * z ^ k.val) =
      (2 - z - z⁻¹) ^ m := by
  classical
  let f : ℤ → ℂ := fun k => (fourierCoeff m k : ℂ) * z ^ k
  have hmNr : (m : ℤ) < N := by exact_mod_cast hmN
  have hpos : (∑ k : Fin N, f (k.val : ℤ)) =
      ∑ k ∈ Finset.Ico (0 : ℤ) (N : ℤ), f k := by
    refine Finset.sum_bij (fun k _ => (k.val : ℤ)) ?_ ?_ ?_ ?_
    · intro k _
      have hk := k.isLt
      apply Finset.mem_Ico.mpr
      constructor <;> omega
    · intro a _ b _ hab
      apply Fin.ext
      change (a.val : ℤ) = (b.val : ℤ) at hab
      omega
    · intro k hk
      have hk' := Finset.mem_Ico.mp hk
      let a : Fin N := ⟨k.toNat, by omega⟩
      refine ⟨a, Finset.mem_univ _, ?_⟩
      dsimp only [a]
      omega
    · intro k _
      rfl
  have hneg : (∑ k : Fin N, f ((k.val : ℤ) - (N : ℤ))) =
      ∑ k ∈ Finset.Ico (-(N : ℤ)) 0, f k := by
    refine Finset.sum_bij (fun k _ => (k.val : ℤ) - (N : ℤ)) ?_ ?_ ?_ ?_
    · intro k _
      have hk := k.isLt
      apply Finset.mem_Ico.mpr
      constructor <;> omega
    · intro a _ b _ hab
      apply Fin.ext
      change (a.val : ℤ) - (N : ℤ) = (b.val : ℤ) - (N : ℤ) at hab
      omega
    · intro k hk
      have hk' := Finset.mem_Ico.mp hk
      let a : Fin N := ⟨(k + (N : ℤ)).toNat, by omega⟩
      refine ⟨a, Finset.mem_univ _, ?_⟩
      dsimp only [a]
      omega
    · intro k _
      rfl
  have hunion : Finset.Ico (-(N : ℤ)) 0 ∪ Finset.Ico (0 : ℤ) (N : ℤ) =
      Finset.Ico (-(N : ℤ)) (N : ℤ) := by
    ext k
    simp only [Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisjoint : Disjoint (Finset.Ico (-(N : ℤ)) 0)
      (Finset.Ico (0 : ℤ) (N : ℤ)) := by
    apply Finset.disjoint_left.mpr
    intro k hk hl
    have hk' := Finset.mem_Ico.mp hk
    have hl' := Finset.mem_Ico.mp hl
    omega
  have hsplit : (∑ k ∈ Finset.Ico (-(N : ℤ)) (N : ℤ), f k) =
      (∑ k ∈ Finset.Ico (0 : ℤ) (N : ℤ), f k) +
        ∑ k ∈ Finset.Ico (-(N : ℤ)) 0, f k := by
    rw [← hunion, Finset.sum_union hdisjoint]
    ring
  have hext : (∑ k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), f k) =
      ∑ k ∈ Finset.Ico (-(N : ℤ)) (N : ℤ), f k := by
    apply Finset.sum_subset
    · intro k hk
      have hk' := Finset.mem_Icc.mp hk
      apply Finset.mem_Ico.mpr
      constructor <;> omega
    · intro k _ hk
      have hlarge : (m : ℤ) < |k| := by
        by_contra hnot
        exact hk (Finset.mem_Icc.mpr (abs_le.mp (le_of_not_gt hnot)))
      simp only [f, fourierCoeff_support m k hlarge, Complex.ofReal_zero, zero_mul]
  calc
    (∑ k : Fin N, (periodicFourierColumn m N k : ℂ) * z ^ k.val) =
        (∑ k : Fin N, f (k.val : ℤ)) +
          ∑ k : Fin N, f ((k.val : ℤ) - (N : ℤ)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      simp only [periodicFourierColumn, Complex.ofReal_add, add_mul, f,
        zpow_sub₀ hz, zpow_natCast, hzN, div_one]
    _ = ∑ k ∈ Finset.Ico (-(N : ℤ)) (N : ℤ), f k := by
      rw [hpos, hneg, ← hsplit]
    _ = ∑ k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), f k := hext.symm
    _ = (2 - z - z⁻¹) ^ m := fourierCoeff_laurent_sum m z hz

private theorem pow_cyclic_sub_mul (N : ℕ) (z : ℂ) (hz : z ≠ 0)
    (hzN : z ^ N = 1) (i j : Fin N) :
    z ^ (j - i).val * z ^ i.val = z ^ j.val := by
  have hp : z ^ (((j - i).val : ℤ)) * z ^ (i.val : ℤ) = z ^ (j.val : ℤ) := by
    rw [← zpow_add₀ hz, Fin.intCast_val_sub_eq_sub_add_ite]
    by_cases hij : i ≤ j
    · simp only [if_pos hij, Nat.cast_zero, add_zero]
      congr 1
      omega
    · simp only [if_neg hij]
      rw [show ((j.val : ℤ) - (i.val : ℤ) + (N : ℤ)) + (i.val : ℤ) =
        (j.val : ℤ) + (N : ℤ) by ring, zpow_add₀ hz]
      simp only [zpow_natCast, hzN, mul_one]
  simpa only [zpow_natCast] using hp

private theorem fourierCirculant_mulVec_geometric (m N : ℕ) (hmN : m < N)
    (z : ℂ) (hz : z ≠ 0) (hzN : z ^ N = 1) :
    ((fourierCirculant m N).map Complex.ofReal).mulVec (fun i : Fin N => z ^ i.val) =
      fun i : Fin N => (2 - z - z⁻¹) ^ m * z ^ i.val := by
  classical
  letI : NeZero N := ⟨by omega⟩
  funext i
  change (∑ j : Fin N, (fourierCirculant m N i j : ℂ) * z ^ j.val) = _
  calc
    (∑ j : Fin N, (fourierCirculant m N i j : ℂ) * z ^ j.val) =
        ∑ j : Fin N, (periodicFourierColumn m N (j - i) : ℂ) * z ^ j.val := by
      apply Finset.sum_congr rfl
      intro j _
      have hs := (fourierCirculant_isHermitian m N hmN).apply j i
      change fourierCirculant m N i j = fourierCirculant m N j i at hs
      rw [hs]
      rfl
    _ = ∑ k : Fin N, (periodicFourierColumn m N k : ℂ) * (z ^ i.val * z ^ k.val) := by
      apply Fintype.sum_equiv (Equiv.subRight i)
      intro j
      simp only [Equiv.subRight_apply]
      rw [← pow_cyclic_sub_mul N z hz hzN i j]
      ring
    _ = (∑ k : Fin N, (periodicFourierColumn m N k : ℂ) * z ^ k.val) * z ^ i.val := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = (2 - z - z⁻¹) ^ m * z ^ i.val := by
      rw [periodicFourierColumn_laurent_sum m N hmN z hz hzN]

theorem fourierCirculant_mulVec_rootOmega (m N : ℕ) (hmN : m < N) (ell : Fin N) :
    ((fourierCirculant m N).map Complex.ofReal).mulVec
        (fun i : Fin N => rootOmega N ell.val ^ i.val) =
      fun i : Fin N =>
        (symbol m (2 * Real.pi * (ell.val : ℝ) / (N : ℝ)) : ℂ) *
          rootOmega N ell.val ^ i.val := by
  have hz : rootOmega N ell.val ≠ 0 := Complex.exp_ne_zero _
  have h := fourierCirculant_mulVec_geometric m N hmN (rootOmega N ell.val) hz
    (rootOmega_pow N ell.val (by omega))
  have hsymbol : (2 - rootOmega N ell.val - (rootOmega N ell.val)⁻¹) ^ m =
      (symbol m (2 * Real.pi * (ell.val : ℝ) / (N : ℝ)) : ℂ) := by
    change (2 - oscillatoryRoot (2 * Real.pi * (ell.val : ℝ) / (N : ℝ)) -
      (oscillatoryRoot (2 * Real.pi * (ell.val : ℝ) / (N : ℝ)))⁻¹) ^ m = _
    rw [oscillatoryRoot_equation, symbol_eq_cosine_power, Complex.ofReal_pow]
  simpa only [hsymbol] using h

/-- The explicit Fourier vectors form a basis even when their eigenvalues
repeat. Thus this identity records the complete spectral multiplicity. -/
theorem fourierCirculant_charpoly_complex (m N : ℕ) (hmN : m < N) :
    ((fourierCirculant m N).map Complex.ofReal).charpoly =
      ∏ ell : Fin N, (Polynomial.X - Polynomial.C
        (symbol m (2 * Real.pi * (ell.val : ℝ) / (N : ℝ)) : ℂ)) := by
  classical
  let A : Matrix (Fin N) (Fin N) ℂ := (fourierCirculant m N).map Complex.ofReal
  let V : Matrix (Fin N) (Fin N) ℂ :=
    (Matrix.vandermonde (fun ell : Fin N => rootOmega N ell.val)).transpose
  let d : Fin N → ℂ := fun ell =>
    (symbol m (2 * Real.pi * (ell.val : ℝ) / (N : ℝ)) : ℂ)
  have hV : IsUnit V.det := by
    apply isUnit_iff_ne_zero.mpr
    dsimp only [V]
    rw [Matrix.det_transpose, Matrix.det_vandermonde_ne_zero_iff]
    exact rootOmega_injective N
  have hAV : A * V = V * Matrix.diagonal d := by
    ext i ell
    rw [Matrix.mul_diagonal]
    change (((fourierCirculant m N).map Complex.ofReal).mulVec
      (fun k : Fin N => rootOmega N ell.val ^ k.val)) i =
      rootOmega N ell.val ^ i.val * d ell
    rw [congrFun (fourierCirculant_mulVec_rootOmega m N hmN ell) i]
    dsimp only [d]
    ring
  change A.charpoly = ∏ ell : Fin N, (Polynomial.X - Polynomial.C (d ell))
  calc
    A.charpoly = ((A * V) * V⁻¹).charpoly := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv V hV, Matrix.mul_one]
    _ = ((V * Matrix.diagonal d) * V⁻¹).charpoly := by rw [hAV]
    _ = (V⁻¹ * (V * Matrix.diagonal d)).charpoly := Matrix.charpoly_mul_comm _ _
    _ = (Matrix.diagonal d).charpoly := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul V hV, Matrix.one_mul]
    _ = ∏ ell : Fin N, (Polynomial.X - Polynomial.C (d ell)) :=
      Matrix.charpoly_diagonal d

#print axioms periodicFourierColumn_laurent_sum
#print axioms fourierCirculant_mulVec_rootOmega
#print axioms fourierCirculant_charpoly_complex

end MF21Restart
