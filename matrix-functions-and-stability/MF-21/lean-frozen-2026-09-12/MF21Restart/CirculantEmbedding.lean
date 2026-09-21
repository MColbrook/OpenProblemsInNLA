import MF21Restart.FourierStencil
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.Data.Fin.Basic

/-!
The literal finite circulant containing the original Toeplitz matrix.
This module proves the periodic entry formula, Hermitian symmetry, and
the exact leading principal block. Its spectrum and interlacing are
separate obligations in `CIRCULANT_INTERLACING_STATEMENTS.md`.
-/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

def periodicFourierColumn (m N : ℕ) (k : Fin N) : ℝ :=
  fourierCoeff m (k.val : ℤ) + fourierCoeff m ((k.val : ℤ) - (N : ℤ))

def fourierCirculant (m N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.circulant (periodicFourierColumn m N)

/-- The exact three-term periodization. Under m<N all other translates
of an entry frequency lie outside the actual Fourier support. -/
theorem fourierCirculant_apply (m N : ℕ) (hmN : m < N) (i j : Fin N) :
    fourierCirculant m N i j =
      fourierCoeff m ((i.val : ℤ) - (j.val : ℤ)) +
      fourierCoeff m ((i.val : ℤ) - (j.val : ℤ) + (N : ℤ)) +
      fourierCoeff m ((i.val : ℤ) - (j.val : ℤ) - (N : ℤ)) := by
  change fourierCoeff m ((i - j).val : ℤ) +
    fourierCoeff m (((i - j).val : ℤ) - (N : ℤ)) = _
  have hmNr : (m : ℤ) < N := by exact_mod_cast hmN
  by_cases hji : j ≤ i
  · have hji' : j.val ≤ i.val := hji
    have hplus : fourierCoeff m ((i.val : ℤ) - (j.val : ℤ) + (N : ℤ)) = 0 := by
      apply fourierCoeff_support
      exact lt_of_lt_of_le (by omega) (le_abs_self _)
    simp only [Fin.intCast_val_sub_eq_sub_add_ite, if_pos hji, Nat.cast_zero, add_zero, hplus]
  · have hij : i.val < j.val := lt_of_not_ge hji
    have hminus : fourierCoeff m ((i.val : ℤ) - (j.val : ℤ) - (N : ℤ)) = 0 := by
      apply fourierCoeff_support
      exact lt_of_lt_of_le (by omega) (neg_le_abs _)
    simp only [Fin.intCast_val_sub_eq_sub_add_ite, if_neg hji,
      add_sub_cancel_right, hminus, add_zero]
    ring

theorem fourierCirculant_isHermitian (m N : ℕ) (hmN : m < N) :
    (fourierCirculant m N).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  change fourierCirculant m N j i = fourierCirculant m N i j
  rw [fourierCirculant_apply m N hmN, fourierCirculant_apply m N hmN]
  have hzero : fourierCoeff m ((j.val : ℤ) - (i.val : ℤ)) =
      fourierCoeff m ((i.val : ℤ) - (j.val : ℤ)) := by
    rw [show (j.val : ℤ) - (i.val : ℤ) = -((i.val : ℤ) - (j.val : ℤ)) by ring,
      fourierCoeff_neg]
  have hplus : fourierCoeff m ((j.val : ℤ) - (i.val : ℤ) + (N : ℤ)) =
      fourierCoeff m ((i.val : ℤ) - (j.val : ℤ) - (N : ℤ)) := by
    rw [show (j.val : ℤ) - (i.val : ℤ) + (N : ℤ) =
      -((i.val : ℤ) - (j.val : ℤ) - (N : ℤ)) by ring, fourierCoeff_neg]
  have hminus : fourierCoeff m ((j.val : ℤ) - (i.val : ℤ) - (N : ℤ)) =
      fourierCoeff m ((i.val : ℤ) - (j.val : ℤ) + (N : ℤ)) := by
    rw [show (j.val : ℤ) - (i.val : ℤ) - (N : ℤ) =
      -((i.val : ℤ) - (j.val : ℤ) + (N : ℤ)) by ring, fourierCoeff_neg]
  rw [hzero, hplus, hminus]
  ring

def circulantIndexEmbedding (m n : ℕ) : Fin n → Fin (n + 2 * m) :=
  Fin.castLE (Nat.le_add_right n (2 * m))

/-- No periodic translate of a leading-block frequency can re-enter
the Fourier bandwidth. This identifies the actual principal block. -/
theorem toeplitz_eq_circulant_submatrix (m n : ℕ) (hm : 1 ≤ m) :
    (fourierCirculant m (n + 2 * m)).submatrix
      (circulantIndexEmbedding m n) (circulantIndexEmbedding m n) = toeplitz m n := by
  have hmN : m < n + 2 * m := by omega
  ext i j
  rw [Matrix.submatrix_apply, fourierCirculant_apply m (n + 2 * m) hmN]
  change fourierCoeff m ((i.val : ℤ) - (j.val : ℤ)) +
    fourierCoeff m ((i.val : ℤ) - (j.val : ℤ) + ((n + 2 * m : ℕ) : ℤ)) +
    fourierCoeff m ((i.val : ℤ) - (j.val : ℤ) - ((n + 2 * m : ℕ) : ℤ)) =
    fourierCoeff m ((i.val : ℤ) - (j.val : ℤ))
  have hi := i.isLt
  have hj := j.isLt
  have hplus : fourierCoeff m
      ((i.val : ℤ) - (j.val : ℤ) + ((n + 2 * m : ℕ) : ℤ)) = 0 := by
    apply fourierCoeff_support
    exact lt_of_lt_of_le (by omega) (le_abs_self _)
  have hminus : fourierCoeff m
      ((i.val : ℤ) - (j.val : ℤ) - ((n + 2 * m : ℕ) : ℤ)) = 0 := by
    apply fourierCoeff_support
    exact lt_of_lt_of_le (by omega) (neg_le_abs _)
  rw [hplus, hminus, add_zero, add_zero]

#print axioms fourierCirculant_apply
#print axioms fourierCirculant_isHermitian
#print axioms toeplitz_eq_circulant_submatrix

end MF21Restart
