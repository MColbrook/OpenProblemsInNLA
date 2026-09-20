import MF21.Definitions
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Int.NatAbs

/-! Fourier-coefficient bridge for MF-21. All statements in this module are
proved; it does not assert the asymptotic theorem. -/

noncomputable section
open scoped BigOperators
open Complex MeasureTheory

namespace MF21Fourier

variable {T : ℝ}

theorem fourier_nat_pow (a : ℤ) (n : ℕ) (x : AddCircle T) :
    fourier a x ^ n = fourier ((n : ℤ) * a) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, fourier_add]

def circleSymbol (m : ℕ) (x : AddCircle T) : ℂ :=
  (2 - fourier 1 x - fourier (-1) x) ^ m

theorem symbol_factor (x : AddCircle T) :
    2 - fourier 1 x - fourier (-1) x =
      -fourier (-1) x * (1 - fourier 1 x) ^ 2 := by
  have h : fourier 1 x * fourier (-1) x = 1 := by
    rw [← fourier_add]
    norm_num [fourier_zero]
  linear_combination (fourier 1 x - 2) * h

theorem circleSymbol_expansion (m : ℕ) (x : AddCircle T) :
    circleSymbol m x =
      ∑ k ∈ Finset.range (2 * m + 1),
        ((-1 : ℂ) ^ (m + k) * ((2 * m).choose k : ℂ)) *
          fourier ((k : ℤ) - m) x := by
  unfold circleSymbol
  rw [symbol_factor, mul_pow, neg_pow, ← pow_mul]
  rw [show 1 - fourier 1 x = -fourier 1 x + 1 by ring]
  rw [add_pow]
  simp only [one_pow, mul_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [neg_pow (fourier 1 x) k]
  rw [fourier_nat_pow, fourier_nat_pow]
  simp only [mul_neg, mul_one, pow_add]
  rw [show fourier ((k : ℤ) - m) x =
    fourier (-(m : ℤ)) x * fourier (k : ℤ) x by
      rw [sub_eq_add_neg, add_comm, fourier_add]]
  ring


variable [Fact (0 < T)]

theorem coefficient_expansion (m : ℕ) (q : ℤ) :
    fourierCoeff (circleSymbol (T := T) m) q =
      ∑ k ∈ Finset.range (2 * m + 1),
        ((-1 : ℂ) ^ (m + k) * ((2 * m).choose k : ℂ)) *
          (if q = (k : ℤ) - m then 1 else 0) := by
  classical
  have hf : circleSymbol (T := T) m =
      ∑ k ∈ Finset.range (2 * m + 1),
        (fun x : AddCircle T ↦
          ((-1 : ℂ) ^ (m + k) * ((2 * m).choose k : ℂ)) *
            fourier ((k : ℤ) - m) x) := by
    funext x
    simp only [Finset.sum_apply]
    exact circleSymbol_expansion m x
  rw [hf, fourierCoeff.sum]
  · simp only [Finset.sum_apply, fourierCoeff.const_mul,
      fourierCoeff_fourier, Pi.single_apply]
  · intro k hk
    exact Continuous.integrable_of_hasCompactSupport
      (continuous_const.mul (fourier ((k : ℤ) - m)).continuous)
      (HasCompactSupport.of_compactSpace _)


theorem coefficient_nonneg (m d : ℕ) :
    fourierCoeff (circleSymbol (T := T) m) (d : ℤ) =
      (-1 : ℂ) ^ d * ((2 * m).choose (m + d) : ℂ) := by
  classical
  rw [coefficient_expansion]
  by_cases hd : d ≤ m
  · rw [Finset.sum_eq_single (m + d)]
    · have he : (d : ℤ) = (m + d : ℕ) - (m : ℤ) := by omega
      rw [if_pos he, mul_one]
      congr 1
      rw [show m + (m + d) = 2 * m + d by omega, pow_add, pow_mul]
      norm_num
    · intro k hk hne
      have he : (d : ℤ) ≠ (k : ℤ) - m := by omega
      simp [he]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  · rw [Nat.choose_eq_zero_of_lt (by omega : 2 * m < m + d)]
    simp only [Nat.cast_zero, mul_zero]
    apply Finset.sum_eq_zero
    intro k hk
    have hkr := Finset.mem_range.mp hk
    have he : (d : ℤ) ≠ (k : ℤ) - m := by omega
    simp [he]


theorem coefficient_neg_nat (m d : ℕ) :
    fourierCoeff (circleSymbol (T := T) m) (-(d : ℤ)) =
      (-1 : ℂ) ^ d * ((2 * m).choose (m + d) : ℂ) := by
  classical
  rw [coefficient_expansion]
  by_cases hd : d ≤ m
  · rw [Finset.sum_eq_single (m - d)]
    · have he : -(d : ℤ) = (m - d : ℕ) - (m : ℤ) := by omega
      rw [if_pos he, mul_one]
      have hc : (2 * m).choose (m - d) = (2 * m).choose (m + d) := by
        rw [← Nat.choose_symm (by omega : m - d ≤ 2 * m)]
        congr 1
        omega
      rw [hc]
      congr 1
      rw [show m + (m - d) = 2 * (m - d) + d by omega, pow_add, pow_mul]
      norm_num
    · intro k hk hne
      have he : -(d : ℤ) ≠ (k : ℤ) - m := by omega
      simp [he]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  · rw [Nat.choose_eq_zero_of_lt (by omega : 2 * m < m + d)]
    simp only [Nat.cast_zero, mul_zero]
    apply Finset.sum_eq_zero
    intro k hk
    have he : -(d : ℤ) ≠ (k : ℤ) - m := by omega
    simp [he]

theorem fourier_two_pi (k : ℤ) (theta : ℝ) :
    @fourier (2 * Real.pi) k (theta : AddCircle (2 * Real.pi)) =
      Complex.exp ((theta : ℂ) * (k : ℂ) * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

theorem circleSymbol_coe (m : ℕ) (theta : ℝ) :
    circleSymbol m (theta : AddCircle (2 * Real.pi)) =
      (MF21Challenge.symbol m theta : ℂ) := by
  have hs := Real.sin_sq_eq_half_sub (theta / 2)
  rw [show 2 * (theta / 2) = theta by ring] at hs
  have hbase : (2 * Real.sin (theta / 2)) ^ 2 = 2 - 2 * Real.cos theta := by
    nlinarith
  have hz : fourier 1 (theta : AddCircle (2 * Real.pi)) +
      fourier (-1) (theta : AddCircle (2 * Real.pi)) =
      2 * (Real.cos theta : ℂ) := by
    rw [fourier_neg, fourier_two_pi]
    simp [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  unfold circleSymbol MF21Challenge.symbol
  rw [show (2 * Real.sin (theta / 2)) ^ (2 * m) =
    (2 - 2 * Real.cos theta) ^ m by rw [pow_mul, hbase]]
  push_cast
  congr 1
  push_cast at hz
  linear_combination -hz


/-- All integer Fourier coefficients, including the zero coefficients outside
of the bandwidth, agree with the explicit real signed-binomial coefficients. -/
theorem coefficient_int (m : ℕ) (q : ℤ) :
    fourierCoeff (circleSymbol (T := T) m) q =
      (MF21Challenge.coefficient m q.natAbs : ℂ) := by
  cases q with
  | ofNat d =>
    simpa [MF21Challenge.coefficient] using coefficient_nonneg (T := T) m d
  | negSucc d =>
    change fourierCoeff (circleSymbol (T := T) m) (-(d + 1 : ℕ) : ℤ) = _
    simpa [MF21Challenge.coefficient] using coefficient_neg_nat (T := T) m (d + 1)

/-- Fourier coefficient in the original real-angle integral convention. -/
def sourceCoefficient (m : ℕ) (q : ℤ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ theta in -Real.pi..Real.pi,
      (MF21Challenge.symbol m theta : ℂ) *
        Complex.exp (-(q : ℂ) * (theta : ℂ) * Complex.I)

instance twoPiPos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The circle formulation is exactly the source's Fourier integral. -/
theorem coefficient_eq_source (m : ℕ) (q : ℤ) :
    fourierCoeff (circleSymbol (T := 2 * Real.pi) m) q = sourceCoefficient m q := by
  rw [fourierCoeff_eq_intervalIntegral _ _ (-Real.pi)]
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
  unfold sourceCoefficient
  rw [Complex.real_smul]
  push_cast
  congr 1
  apply intervalIntegral.integral_congr
  intro theta htheta
  change fourier (-q) (theta : AddCircle (2 * Real.pi)) * circleSymbol m (theta : AddCircle (2 * Real.pi)) = _
  rw [circleSymbol_coe, fourier_two_pi]
  simp only [Int.cast_neg]
  rw [mul_comm]
  congr 1
  congr 1
  ring

/-- Identification of the actual Fourier coefficients; no Fourier bridge is
left as an assumption in the matrix statement. -/
theorem sourceCoefficient_eq (m : ℕ) (q : ℤ) :
    sourceCoefficient m q = (MF21Challenge.coefficient m q.natAbs : ℂ) := by
  rw [← coefficient_eq_source]
  exact coefficient_int m q

/-- Entrywise identification with the Fourier-defined Toeplitz matrix. -/
theorem toeplitz_eq_source (m n : ℕ) (i j : Fin n) :
    (MF21Challenge.toeplitz m n i j : ℂ) =
      sourceCoefficient m ((i.val : ℤ) - j.val) := by
  rw [sourceCoefficient_eq]
  congr 1
  unfold MF21Challenge.toeplitz
  rcases le_total i.val j.val with h | h
  · rw [Nat.dist_eq_sub_of_le h, Int.natAbs_natCast_sub_natCast_of_le h]
  · rw [Nat.dist_eq_sub_of_le_right h, Int.natAbs_natCast_sub_natCast_of_ge h]

#print axioms circleSymbol_expansion
#print axioms coefficient_expansion
#print axioms coefficient_nonneg
#print axioms coefficient_neg_nat
#print axioms circleSymbol_coe

#print axioms sourceCoefficient_eq
#print axioms toeplitz_eq_source

end MF21Fourier
