import MF21.CirculantOrdering
import Mathlib.Analysis.PSeries

/-! Actual eigenvalue bounds from the principal circulant, including the
summable reciprocal majorant required for the trace obstruction. -/

open Matrix Finset
open scoped BigOperators
noncomputable section
namespace MF21Circulant

theorem orderedSymbol_lower (m N : ℕ) [NeZero N] (j : Fin N) :
    (4*(foldedIndex j : ℝ)/N)^(2*m) ≤ orderedSymbol m N j := by
  have hN : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hfold : 2 * foldedIndex j ≤ N := by unfold foldedIndex; have := j.isLt; omega
  have hfold' : (2 : ℝ) * (foldedIndex j : ℝ) ≤ N := by exact_mod_cast hfold
  have h0 : 0 ≤ 2*Real.pi*(foldedIndex j : ℝ)/N/2 := by positivity
  have htop : 2*Real.pi*(foldedIndex j : ℝ)/N/2 ≤ Real.pi/2 := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    apply (div_le_iff₀ hN).mpr
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_le_sin h0 htop
  have heq : 2 * (2 / Real.pi * (2*Real.pi*(foldedIndex j : ℝ)/N/2)) =
      4*(foldedIndex j : ℝ)/N := by field_simp; ring
  have hbase := mul_le_mul_of_nonneg_left hsin (by norm_num : (0 : ℝ) ≤ 2)
  rw [heq] at hbase
  exact pow_le_pow_left₀ (by positivity) hbase (2*m)

theorem orderedSymbol_upper (m N : ℕ) [NeZero N] (j : Fin N) :
    orderedSymbol m N j ≤ (Real.pi*(j.val+1)/N)^(2*m) := by
  have hN : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hfold : 2 * foldedIndex j ≤ N := by unfold foldedIndex; have := j.isLt; omega
  have hfold' : (2 : ℝ) * (foldedIndex j : ℝ) ≤ N := by exact_mod_cast hfold
  have h0 : 0 ≤ 2*Real.pi*(foldedIndex j : ℝ)/N/2 := by positivity
  have htop : 2*Real.pi*(foldedIndex j : ℝ)/N/2 ≤ Real.pi := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    apply (div_le_iff₀ hN).mpr
    nlinarith [Real.pi_pos]
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi h0 htop
  have hsin := Real.sin_le h0
  have hf : (2 : ℝ) * (foldedIndex j : ℝ) ≤ j.val + 1 := by
    exact_mod_cast (show 2 * foldedIndex j ≤ j.val + 1 by unfold foldedIndex; omega)
  have hbase : 2 * Real.sin (2*Real.pi*(foldedIndex j : ℝ)/N/2) ≤
      Real.pi*(j.val+1)/N := by
    calc
      _ ≤ 2 * (2*Real.pi*(foldedIndex j : ℝ)/N/2) := by linarith
      _ = 2*Real.pi*(foldedIndex j : ℝ)/N := by ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hN)
        nlinarith [mul_le_mul_of_nonneg_left hf (le_of_lt Real.pi_pos)]
  exact pow_le_pow_left₀ (by positivity) hbase (2*m)

theorem toeplitz_eigenvalue_lower (m n : ℕ) (j : Fin n) :
    (4*((j.val+1)/2 : ℕ)/((n : ℝ)+2*m))^(2*m) ≤ MF21Challenge.eigenvalue m n j := by
  let : NeZero (n+2*m) := ⟨by have := j.isLt; omega⟩
  have h := (toeplitz_circulant_interlacing m n (n+2*m) le_rfl j).1
  have hl := orderedSymbol_lower m (n+2*m) (⟨j.val, by omega⟩ : Fin (n+2*m))
  have hl' : (4*((j.val+1)/2 : ℕ)/((n : ℝ)+2*m))^(2*m) ≤
      orderedSymbol m (n+2*m) ⟨j.val, by omega⟩ := by
    simpa only [foldedIndex, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hl
  exact hl'.trans h

theorem toeplitz_eigenvalue_upper (m n : ℕ) (j : Fin n) :
    MF21Challenge.eigenvalue m n j ≤
      (Real.pi*((j.val : ℝ)+1+2*m)/(n : ℝ))^(2*m) := by
  let : NeZero (n+2*m) := ⟨by have := j.isLt; omega⟩
  have h := (toeplitz_circulant_interlacing m n (n+2*m) le_rfl j).2
  have hu := orderedSymbol_upper m (n+2*m)
    (⟨n+2*m-n+j.val, by omega⟩ : Fin (n+2*m))
  refine h.trans (hu.trans ?_)
  apply pow_le_pow_left₀ (by positivity)
  have hn : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by have := j.isLt; omega)
  have he : n+2*m-n+j.val = j.val+2*m := by omega
  simp only [he, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [show (j.val : ℝ)+2*m+1 = j.val+1+2*m by ring]
  apply div_le_div_of_nonneg_left (by positivity) hn
  linarith [show (0 : ℝ) ≤ m by positivity]

theorem scaled_reciprocal_majorant (m n : ℕ) (hm : 1 ≤ m) (j : Fin n)
    (hj : 1 ≤ j.val) :
    (((n : ℝ)+2)^(2*m) * MF21Challenge.eigenvalue m n j)⁻¹ ≤
      (m : ℝ)^(2*m) / ((j.val : ℝ)+1)^(2*m) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hN : 0 < (n : ℝ)+2*m := by positivity
  have hnp : 0 < (n : ℝ)+2 := by positivity
  have hjp : 0 < (j.val : ℝ)+1 := by positivity
  have hNm : (n : ℝ)+2*m ≤ m*((n : ℝ)+2) := by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hjr : (j.val : ℝ)+1 ≤ 4*((j.val+1)/2 : ℕ) := by
    exact_mod_cast (show j.val+1 ≤ 4*((j.val+1)/2) by omega)
  have hb : ((j.val : ℝ)+1)/(m*((n : ℝ)+2)) ≤
      4*((j.val+1)/2 : ℕ)/((n : ℝ)+2*m) := by
    calc
      _ ≤ ((j.val : ℝ)+1)/((n : ℝ)+2*m) :=
        div_le_div_of_nonneg_left (le_of_lt hjp) hN hNm
      _ ≤ _ := div_le_div_of_nonneg_right hjr (le_of_lt hN)
  have hp := (pow_le_pow_left₀ (by positivity) hb (2*m)).trans
    (toeplitz_eigenvalue_lower m n j)
  have hscaled : (((j.val : ℝ)+1)/m)^(2*m) ≤
      ((n : ℝ)+2)^(2*m) * MF21Challenge.eigenvalue m n j := by
    calc
      _ = ((n : ℝ)+2)^(2*m) * (((j.val : ℝ)+1)/(m*((n : ℝ)+2)))^(2*m) := by
        rw [← mul_pow]
        congr 1
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
  have hpos : 0 < (((j.val : ℝ)+1)/m)^(2*m) := by positivity
  have hh := one_div_le_one_div_of_le hpos hscaled
  simpa only [one_div, div_pow, inv_div] using hh

theorem reciprocal_majorant_summable (m : ℕ) (hm : 1 ≤ m) :
    Summable (fun j : ℕ ↦ (m : ℝ)^(2*m) / ((j : ℝ)+1)^(2*m)) := by
  have hp : Summable (fun j : ℕ ↦ 1 / (j : ℝ)^(2*m)) :=
    (Real.summable_one_div_nat_pow).mpr (by omega)
  have hs := (summable_nat_add_iff 1).mpr hp
  simpa only [Nat.cast_add, Nat.cast_one, mul_one_div] using hs.mul_left ((m : ℝ)^(2*m))

theorem orderedSymbol_strict_upper (m N : ℕ) [NeZero N] (hm : 0 < m)
    (hodd : Odd N) (j : Fin N) : orderedSymbol m N j < (4 : ℝ)^m := by
  have hN : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hfold : 2 * foldedIndex j < N := by
    have hj := j.isLt
    have ho := Nat.odd_iff.mp hodd
    unfold foldedIndex
    omega
  have hfold' : (2 : ℝ) * (foldedIndex j : ℝ) < N := by exact_mod_cast hfold
  have h0 : 0 ≤ 2*Real.pi*(foldedIndex j : ℝ)/N/2 := by positivity
  have htop : 2*Real.pi*(foldedIndex j : ℝ)/N/2 < Real.pi/2 := by
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    apply (div_lt_iff₀ hN).mpr
    nlinarith [Real.pi_pos]
  have hsin : Real.sin (2*Real.pi*(foldedIndex j : ℝ)/N/2) < 1 := by
    simpa only [Real.sin_pi_div_two] using Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (show -(Real.pi/2) ≤ 2*Real.pi*(foldedIndex j : ℝ)/N/2 by linarith [Real.pi_pos])
      (le_refl (Real.pi/2)) htop
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi h0
    (show 2*Real.pi*(foldedIndex j : ℝ)/N/2 ≤ Real.pi by linarith [Real.pi_pos])
  calc
    orderedSymbol m N j < (2 : ℝ)^(2*m) := by
      exact pow_lt_pow_left₀ (by linarith) (by positivity) (by omega : 2*m ≠ 0)
    _ = (4 : ℝ)^m := by rw [pow_mul]; norm_num

/-- Strict spectral endpoints for the actual Toeplitz matrices. Taking an
odd principal circulant keeps every comparison sample strictly below pi. -/
theorem toeplitz_eigenvalue_strict_upper (m n : ℕ) (hm : 0 < m) (j : Fin n) :
    MF21Challenge.eigenvalue m n j < (4 : ℝ)^m := by
  let N := 2*(n+2*m)+1
  let : NeZero N := ⟨by dsimp [N]; omega⟩
  have hN : n+2*m ≤ N := by dsimp [N]; omega
  have ho : Odd N := ⟨n+2*m, by dsimp [N]⟩
  exact (toeplitz_circulant_interlacing m n N hN j).2.trans_lt
    (orderedSymbol_strict_upper m N hm ho _)

end MF21Circulant

#print axioms MF21Circulant.toeplitz_eigenvalue_lower
#print axioms MF21Circulant.toeplitz_eigenvalue_upper
#print axioms MF21Circulant.scaled_reciprocal_majorant
#print axioms MF21Circulant.reciprocal_majorant_summable
#print axioms MF21Circulant.toeplitz_eigenvalue_strict_upper
