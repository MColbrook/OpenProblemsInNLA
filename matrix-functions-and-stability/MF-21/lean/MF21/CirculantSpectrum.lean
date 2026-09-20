import MF21.CompressionInterlacing
import MF21.FourierCoefficients
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.LinearAlgebra.Matrix.Circulant

/-! Discrete Fourier diagonalization of circulants, for the actual principal
circulant comparison in MF-21. -/

open Matrix Finset Polynomial
open scoped BigOperators
noncomputable section
namespace MF21Circulant

variable {N : ℕ} [NeZero N]

def fourierMatrix : Matrix (ZMod N) (ZMod N) ℂ :=
  fun i j ↦ ZMod.stdAddChar (i * j)

theorem fourierMatrix_mulVec (v : ZMod N → ℂ) (i : ZMod N) :
    (fourierMatrix *ᵥ v) i = ZMod.dft v (-i) := by
  simp only [fourierMatrix, Matrix.mulVec, dotProduct, ZMod.dft_apply,
    mul_neg, neg_neg, smul_eq_mul]
  apply sum_congr rfl
  intro j _
  rw [mul_comm i j]

theorem fourierMatrix_isUnit : IsUnit (fourierMatrix (N := N)) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w h
  apply ZMod.dft.injective
  funext i
  have hi := congrFun h (-i)
  simpa only [fourierMatrix_mulVec, neg_neg] using hi

theorem circulant_mul_fourierMatrix (v : ZMod N → ℂ) :
    circulant v * fourierMatrix = fourierMatrix * diagonal (ZMod.dft v) := by
  ext i l
  rw [Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, circulant_apply, fourierMatrix]
  have hr := Equiv.sum_comp (Equiv.subLeft i)
    (fun j : ZMod N ↦ v (i - j) * ZMod.stdAddChar (j * l))
  calc
    (∑ j, v (i - j) * ZMod.stdAddChar (j * l)) =
        ∑ t, v t * ZMod.stdAddChar ((i - t) * l) := by
      simpa only [Equiv.subLeft_apply, sub_sub_cancel] using hr.symm
    _ = ZMod.stdAddChar (i * l) * ZMod.dft v l := by
      simp only [ZMod.dft_apply, smul_eq_mul, mul_sum]
      apply sum_congr rfl
      intro t _
      rw [sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring

theorem circulant_charpoly (v : ZMod N → ℂ) :
    (circulant v).charpoly = ∏ l : ZMod N, (X - C (ZMod.dft v l)) := by
  obtain ⟨u, hu⟩ := fourierMatrix_isUnit (N := N)
  have h := circulant_mul_fourierMatrix v
  rw [← hu] at h
  have hs : circulant v = (u : Matrix (ZMod N) (ZMod N) ℂ) *
      diagonal (ZMod.dft v) * (↑(u⁻¹) : Matrix (ZMod N) (ZMod N) ℂ) := by
    have he := congrArg (fun M : Matrix (ZMod N) (ZMod N) ℂ ↦ M * (↑(u⁻¹) : Matrix (ZMod N) (ZMod N) ℂ)) h
    simpa only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] using he
  rw [hs, Matrix.coe_units_inv, charpoly_units_conj, charpoly_diagonal]

def centralWeight (m k : ℕ) : ℝ :=
  (-1 : ℝ)^(m + k) * ((2*m).choose k : ℝ)

def periodicCoefficient (m : ℕ) (j : ZMod N) : ℝ :=
  ∑ k ∈ range (2*m+1), if j = (k : ZMod N) - m then centralWeight m k else 0

def angle (l : ZMod N) : ℝ := 2 * Real.pi * l.val / N

theorem character_fourier_phase (q : ℤ) (l : ZMod N) :
    ZMod.stdAddChar (-(q : ZMod N) * l) =
      fourier q ((-angle l : ℝ) : AddCircle (2 * Real.pi)) := by
  rw [MF21Fourier.fourier_two_pi]
  have h := ZMod.stdAddChar_coe (N := N) (-q * (l.val : ℤ))
  simp only [Int.cast_mul, Int.cast_neg, Int.cast_natCast, ZMod.natCast_zmod_val] at h
  rw [h]
  congr 1
  simp only [angle, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_natCast, Complex.ofReal_ofNat]
  ring

theorem symbol_neg (m : ℕ) (t : ℝ) : MF21Challenge.symbol m (-t) = MF21Challenge.symbol m t := by
  simp only [MF21Challenge.symbol, neg_div, Real.sin_neg, mul_neg,
    even_two_mul, Even.neg_pow]

theorem periodicCoefficient_dft (m : ℕ) (l : ZMod N) :
    ZMod.dft (fun j ↦ (periodicCoefficient m j : ℂ)) l =
      (MF21Challenge.symbol m (angle l) : ℂ) := by
  have hsum : ZMod.dft (fun j ↦ (periodicCoefficient m j : ℂ)) l =
      ∑ k ∈ range (2*m+1), (centralWeight m k : ℂ) *
        ZMod.stdAddChar (-((k : ZMod N) - (m : ZMod N)) * l) := by
    simp only [ZMod.dft_apply, periodicCoefficient, Complex.ofReal_sum,
      apply_ite Complex.ofReal, Complex.ofReal_zero, smul_eq_mul, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    simp only [mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]
    simp only [neg_mul]
    ring
  rw [hsum]
  have hfour := MF21Fourier.circleSymbol_expansion m
    ((-angle l : ℝ) : AddCircle (2 * Real.pi))
  rw [MF21Fourier.circleSymbol_coe, symbol_neg] at hfour
  rw [hfour]
  apply sum_congr rfl
  intro k _
  have hchar := character_fourier_phase ((k : ℤ) - m) l
  simp only [Int.cast_sub, Int.cast_natCast] at hchar
  rw [hchar]
  simp only [centralWeight, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_one, Complex.ofReal_natCast]

theorem centralWeight_reflect (m k : ℕ) (hk : k ≤ 2*m) :
    centralWeight m (2*m-k) = centralWeight m k := by
  unfold centralWeight
  rw [Nat.choose_symm hk]
  congr 1
  rw [neg_one_pow_eq_pow_mod_two (m + (2*m-k)), neg_one_pow_eq_pow_mod_two (m+k)]
  congr 1
  omega

omit [NeZero N] in
theorem periodicCoefficient_neg (m : ℕ) (j : ZMod N) :
    periodicCoefficient m (-j) = periodicCoefficient m j := by
  unfold periodicCoefficient
  rw [← sum_range_reflect (fun k ↦
    if -j = (k : ZMod N) - m then centralWeight m k else 0) (2*m+1)]
  apply sum_congr rfl
  intro k hk
  have hk' : k ≤ 2*m := by simpa using hk
  rw [show 2*m+1-1-k = 2*m-k by omega, centralWeight_reflect m k hk', Nat.cast_sub hk']
  have he : (-j = (2*m : ℕ) - (k : ZMod N) - m) ↔ j = (k : ZMod N) - m := by
    push_cast
    constructor <;> intro h <;> linear_combination -h
  simp only [he]

def realCirculant (m : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  (circulant (periodicCoefficient (N := N) m)).submatrix (ZMod.finEquiv N) (ZMod.finEquiv N)

theorem realCirculant_isHermitian (m : ℕ) : (realCirculant (N := N) m).IsHermitian := by
  apply Matrix.IsHermitian.submatrix
  rw [Matrix.isHermitian_iff_isSymm, circulant_isSymm_iff]
  exact periodicCoefficient_neg m

omit [NeZero N] in
theorem periodicCoefficient_principal (m n : ℕ) (hN : n + 2*m ≤ N) (i j : Fin n) :
    periodicCoefficient m ((i.val : ZMod N) - (j.val : ZMod N)) = MF21Challenge.toeplitz m n i j := by
  apply Complex.ofReal_injective
  rw [MF21Fourier.toeplitz_eq_source, ← MF21Fourier.coefficient_eq_source,
    MF21Fourier.coefficient_expansion]
  simp only [periodicCoefficient, Complex.ofReal_sum]
  apply sum_congr rfl
  intro k hk
  have hk' : k ≤ 2*m := by simpa using hk
  have he : ((i.val : ZMod N) - (j.val : ZMod N) = (k : ZMod N) - (m : ZMod N)) ↔
      (i.val : ℤ) - j.val = (k : ℤ) - m := by
    constructor
    · intro h
      have he' : ((i.val+m : ℕ) : ZMod N) = ((k+j.val : ℕ) : ZMod N) := by
        push_cast
        linear_combination h
      have hiN : i.val+m < N := by omega
      have hkN : k+j.val < N := by omega
      have hval := congrArg ZMod.val he'
      rw [ZMod.val_natCast_of_lt hiN, ZMod.val_natCast_of_lt hkN] at hval
      omega
    · intro h
      have he' : i.val+m = k+j.val := by omega
      have hc := congrArg (fun a : ℕ ↦ (a : ZMod N)) he'
      push_cast at hc
      linear_combination hc
  simp only [he]
  split_ifs <;> simp [centralWeight]

theorem val_finEquiv (i : Fin N) : (ZMod.finEquiv N i).val = i.val := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ N => rfl

theorem finEquiv_eq_natCast (i : Fin N) : ZMod.finEquiv N i = (i.val : ZMod N) := by
  rw [← ZMod.natCast_zmod_val (ZMod.finEquiv N i), val_finEquiv]

theorem realCirculant_principal (m n : ℕ) (hN : n + 2*m ≤ N) :
    (realCirculant (N := N) m).submatrix (Fin.castLE (by omega : n ≤ N))
      (Fin.castLE (by omega : n ≤ N)) = MF21Challenge.toeplitz m n := by
  ext i j
  simpa only [realCirculant, Matrix.submatrix_apply, circulant_apply,
    finEquiv_eq_natCast, Fin.val_castLE] using periodicCoefficient_principal m n hN i j

theorem realCirculant_charpoly (m : ℕ) :
    (realCirculant (N := N) m).charpoly =
      ∏ l : Fin N, (X - C (MF21Challenge.symbol m (2*Real.pi*l.val/N))) := by
  have hc : (circulant (periodicCoefficient (N := N) m)).charpoly =
      ∏ l : ZMod N, (X - C (MF21Challenge.symbol m (angle l))) := by
    apply Polynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
    rw [← Matrix.charpoly_map]
    have hh := circulant_charpoly (fun j : ZMod N ↦ (periodicCoefficient m j : ℂ))
    simp only [periodicCoefficient_dft] at hh
    simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      Complex.ofRealHom_eq_coe, map_circulant]
    exact hh
  have hr := Matrix.charpoly_reindex (ZMod.finEquiv N).toEquiv.symm
    (circulant (periodicCoefficient (N := N) m))
  change (realCirculant (N := N) m).charpoly = _ at hr
  rw [hr, hc]
  have hp := (ZMod.finEquiv N).toEquiv.prod_comp
    (fun l : ZMod N ↦ X - C (MF21Challenge.symbol m (angle l)))
  convert hp.symm using 1
  apply prod_congr rfl
  intro i _
  congr 3
  change 2*Real.pi*i.val/N = 2*Real.pi*(ZMod.finEquiv N i).val/N
  rw [val_finEquiv]

end MF21Circulant

#print axioms MF21Circulant.fourierMatrix_isUnit
#print axioms MF21Circulant.circulant_charpoly
#print axioms MF21Circulant.periodicCoefficient_dft
#print axioms MF21Circulant.realCirculant_isHermitian
#print axioms MF21Circulant.periodicCoefficient_principal
#print axioms MF21Circulant.realCirculant_principal
#print axioms MF21Circulant.realCirculant_charpoly
