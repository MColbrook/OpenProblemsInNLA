import MF21Restart.CirculantOrder
import MF21Restart.HermitianInterlacing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Actual one-based Toeplitz eigenvalue bounds from the proved circulant
embedding and proved Hermitian principal-block interlacing. The final
corollaries supply a fixed-prefix estimate and a reciprocal tail majorant.
See the prior lock `CIRCULANT_BOUND_STATEMENTS.md`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

private theorem ascendingValue_toeplitz (m n : ℕ) (i : Fin n) :
    hermitianAscendingValue (toeplitz m n) (toeplitz_isHermitian m n) i =
      orderedEigenvalue m n i := by
  have hlist := hermitianAscendingValue_sorted (toeplitz m n) (toeplitz_isHermitian m n)
  change orderedEigenvalueList m n =
    List.ofFn (hermitianAscendingValue (toeplitz m n) (toeplitz_isHermitian m n)) at hlist
  have hordered : List.ofFn (orderedEigenvalue m n) = orderedEigenvalueList m n := by
    apply List.ext_getElem
    · simp [orderedEigenvalueList]
    · intro k hk hl
      simp only [List.getElem_ofFn]
      rfl
  exact congrFun (List.ofFn_injective (hlist.symm.trans hordered.symm)) i

private theorem ascendingValue_circulant (m N : ℕ) (hm : 1 ≤ m) (hmN : m < N)
    (i : Fin N) :
    hermitianAscendingValue (fourierCirculant m N) (fourierCirculant_isHermitian m N hmN) i =
      circulantOrderedValue m N (i.val + 1) := by
  have hlist := (hermitianAscendingValue_sorted (fourierCirculant m N)
    (fourierCirculant_isHermitian m N hmN)).symm.trans
      (fourierCirculant_sorted_eigenvalues m N hm hmN)
  exact congrFun (List.ofFn_injective hlist) i

theorem eigenvalue_circulant_interlacing
    (m n j : ℕ) (hm : 1 ≤ m) (hj : 1 ≤ j) (hjn : j ≤ n) :
    circulantOrderedValue m (n + 2 * m) j ≤ eigenvalue m n j ∧
      eigenvalue m n j ≤ circulantOrderedValue m (n + 2 * m) (j + 2 * m) := by
  have hnN : n ≤ n + 2 * m := by omega
  have hmN : m < n + 2 * m := by omega
  let i : Fin n := ⟨j - 1, by omega⟩
  have hblock : (fourierCirculant m (n + 2 * m)).submatrix
      (Fin.castLE hnN) (Fin.castLE hnN) = toeplitz m n :=
    toeplitz_eq_circulant_submatrix m n hm
  have h := hermitian_principal_interlacing n (n + 2 * m) hnN
    (toeplitz m n) (fourierCirculant m (n + 2 * m))
    (toeplitz_isHermitian m n) (fourierCirculant_isHermitian m (n + 2 * m) hmN) hblock i
  rw [ascendingValue_toeplitz, ascendingValue_circulant m (n + 2 * m) hm hmN,
    ascendingValue_circulant m (n + 2 * m) hm hmN] at h
  have hleft : (Fin.castLE hnN i).val + 1 = j := by
    change j - 1 + 1 = j
    omega
  have hright : i.val + ((n + 2 * m) - n) + 1 = j + 2 * m := by dsimp only [i]; omega
  rw [hleft, hright] at h
  rw [eigenvalue_in_range hj hjn]
  exact h

private theorem circulantOrderedValue_sine_bounds
    (m N j : ℕ) (hN : 0 < N) (hjN : j ≤ N) :
    (4 * ((j / 2 : ℕ) : ℝ) / (N : ℝ)) ^ (2 * m) ≤ circulantOrderedValue m N j ∧
      circulantOrderedValue m N j ≤ (Real.pi * (j : ℝ) / (N : ℝ)) ^ (2 * m) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let t : ℝ := Real.pi * ((j / 2 : ℕ) : ℝ) / (N : ℝ)
  have ht0 : 0 ≤ t := by dsimp only [t]; positivity
  have hhalf : (2 : ℝ) * ((j / 2 : ℕ) : ℝ) ≤ N := by
    exact_mod_cast (show 2 * (j / 2) ≤ N by omega)
  have htpi : t ≤ Real.pi / 2 := by
    apply (div_le_iff₀ hNr).mpr
    nlinarith [Real.pi_pos]
  have hsin : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [Real.pi_pos])
  have hvalue : circulantOrderedValue m N j = (2 * Real.sin t) ^ (2 * m) := by
    have hangle : 2 * Real.pi * ((j / 2 : ℕ) : ℝ) / (N : ℝ) / 2 = t := by
      dsimp only [t]
      ring
    simp only [circulantOrderedValue, symbol, hangle]
  have hlower : 4 * ((j / 2 : ℕ) : ℝ) / (N : ℝ) ≤ 2 * Real.sin t := by
    have hs := mul_le_mul_of_nonneg_left (Real.mul_le_sin ht0 htpi) (by norm_num : (0 : ℝ) ≤ 2)
    have hid : 2 * (2 / Real.pi * t) = 4 * ((j / 2 : ℕ) : ℝ) / (N : ℝ) := by
      dsimp only [t]
      field_simp [Real.pi_ne_zero, hNr.ne']
      <;> ring
    rwa [hid] at hs
  have hupper : 2 * Real.sin t ≤ Real.pi * (j : ℝ) / (N : ℝ) := by
    have hjhalf : (2 : ℝ) * ((j / 2 : ℕ) : ℝ) ≤ j := by
      exact_mod_cast (show 2 * (j / 2) ≤ j by omega)
    calc
      _ ≤ 2 * t := mul_le_mul_of_nonneg_left (Real.sin_le ht0) (by norm_num)
      _ = (Real.pi * (2 * ((j / 2 : ℕ) : ℝ))) / (N : ℝ) := by dsimp only [t]; ring
      _ ≤ Real.pi * (j : ℝ) / (N : ℝ) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hjhalf Real.pi_pos.le) hNr.le
  rw [hvalue]
  exact ⟨pow_le_pow_left₀ (by positivity) hlower _,
    pow_le_pow_left₀ (by positivity) hupper _⟩

theorem eigenvalue_circulant_power_bounds
    (m n j : ℕ) (hm : 1 ≤ m) (hj : 1 ≤ j) (hjn : j ≤ n) :
    (4 * ((j / 2 : ℕ) : ℝ) / ((n + 2 * m : ℕ) : ℝ)) ^ (2 * m) ≤ eigenvalue m n j ∧
      eigenvalue m n j ≤
        (Real.pi * ((j + 2 * m : ℕ) : ℝ) / ((n + 2 * m : ℕ) : ℝ)) ^ (2 * m) := by
  have h := eigenvalue_circulant_interlacing m n j hm hj hjn
  have hl := circulantOrderedValue_sine_bounds m (n + 2 * m) j (by omega) (by omega)
  have hu := circulantOrderedValue_sine_bounds m (n + 2 * m) (j + 2 * m) (by omega) (by omega)
  exact ⟨hl.1.trans h.1, h.2.trans hu.2⟩

theorem eigenvalue_circulant_lower_bound
    (m n j : ℕ) (hm : 1 ≤ m) (hj : 2 ≤ j) (hjn : j ≤ n) :
    (4 * (j : ℝ) / (3 * ((n + 2 * m : ℕ) : ℝ))) ^ (2 * m) ≤ eigenvalue m n j := by
  have hl := (eigenvalue_circulant_power_bounds m n j hm (by omega) hjn).1
  have hjthird : (j : ℝ) ≤ 3 * ((j / 2 : ℕ) : ℝ) := by
    exact_mod_cast (show j ≤ 3 * (j / 2) by omega)
  have hN : (0 : ℝ) < ((n + 2 * m : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n + 2 * m by omega)
  have hbase : 4 * (j : ℝ) / (3 * ((n + 2 * m : ℕ) : ℝ)) ≤
      4 * ((j / 2 : ℕ) : ℝ) / ((n + 2 * m : ℕ) : ℝ) := by
    rw [show 4 * (j : ℝ) / (3 * ((n + 2 * m : ℕ) : ℝ)) =
      ((4 / 3 : ℝ) * (j : ℝ)) / ((n + 2 * m : ℕ) : ℝ) by ring]
    exact div_le_div_of_nonneg_right (by linarith) hN.le
  exact (pow_le_pow_left₀ (by positivity) hbase (2 * m)).trans hl

/-- The fixed finite prefix required by the uniform Taylor assembly. -/
theorem eigenvalue_fixed_prefix_bound (m : ℕ) (hm : 1 ≤ m) (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ,
      1 ≤ j → j < J → j ≤ n →
        |eigenvalue m n j| ≤ C * (1 / (n + 2 : ℝ)) ^ (2 * m) := by
  let C : ℝ := (Real.pi * ((J + 2 * m : ℕ) : ℝ)) ^ (2 * m)
  have hC : 0 < C := by
    apply pow_pos
    exact mul_pos Real.pi_pos (by exact_mod_cast (show 0 < J + 2 * m by omega))
  refine ⟨C, hC, 1, ?_⟩
  intro n hn j hj hjJ hjn
  have heig := eigenvalue_strict_spectral_enclosure m n j hm hj hjn
  rw [abs_of_pos heig.1]
  have hupper := (eigenvalue_circulant_power_bounds m n j hm hj hjn).2
  have hN : (0 : ℝ) < n + 2 := by positivity
  have hden : (n + 2 : ℝ) ≤ ((n + 2 * m : ℕ) : ℝ) := by
    exact_mod_cast (show n + 2 ≤ n + 2 * m by omega)
  have hnum : Real.pi * ((j + 2 * m : ℕ) : ℝ) ≤
      Real.pi * ((J + 2 * m : ℕ) : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
    exact_mod_cast (show j + 2 * m ≤ J + 2 * m by omega)
  have hratio : Real.pi * ((j + 2 * m : ℕ) : ℝ) / ((n + 2 * m : ℕ) : ℝ) ≤
      Real.pi * ((J + 2 * m : ℕ) : ℝ) / (n + 2 : ℝ) := by
    calc
      _ ≤ Real.pi * ((j + 2 * m : ℕ) : ℝ) / (n + 2 : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hN hden
      _ ≤ _ := div_le_div_of_nonneg_right hnum hN.le
  calc
    eigenvalue m n j ≤
        (Real.pi * ((j + 2 * m : ℕ) : ℝ) / ((n + 2 * m : ℕ) : ℝ)) ^ (2 * m) := hupper
    _ ≤ (Real.pi * ((J + 2 * m : ℕ) : ℝ) / (n + 2 : ℝ)) ^ (2 * m) :=
      pow_le_pow_left₀ (by positivity) hratio _
    _ = C * (1 / (n + 2 : ℝ)) ^ (2 * m) := by
      dsimp only [C]
      rw [div_pow, one_div_pow]
      ring

/-- The explicit j-power majorant needed for the reciprocal trace tail. -/
theorem eigenvalue_reciprocal_tail_majorant
    (m n j : ℕ) (hm : 1 ≤ m) (hj : 2 ≤ j) (hjn : j ≤ n) :
    (1 / (n + 2 : ℝ)) ^ (2 * m) / eigenvalue m n j ≤
      (3 * (m : ℝ) / 4) ^ (2 * m) * ((j : ℝ) ^ (2 * m))⁻¹ := by
  have hN : (0 : ℝ) < n + 2 := by positivity
  have hNm : (0 : ℝ) < ((n + 2 * m : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n + 2 * m by omega)
  have hjr : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hratio : ((n + 2 * m : ℕ) : ℝ) / (n + 2 : ℝ) ≤ m := by
    apply (div_le_iff₀ hN).mpr
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.mpr hmr) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  let low : ℝ := 4 * (j : ℝ) / (3 * ((n + 2 * m : ℕ) : ℝ))
  have hlow : 0 < low := by dsimp only [low]; positivity
  have hlowEig : low ^ (2 * m) ≤ eigenvalue m n j :=
    eigenvalue_circulant_lower_bound m n j hm hj hjn
  have hbase : (1 / (n + 2 : ℝ)) / low ≤ (3 * (m : ℝ) / 4) / (j : ℝ) := by
    calc
      (1 / (n + 2 : ℝ)) / low =
          (3 / (4 * (j : ℝ))) * (((n + 2 * m : ℕ) : ℝ) / (n + 2 : ℝ)) := by
        dsimp only [low]
        field_simp [hN.ne', hNm.ne', hjr.ne']
        <;> ring
      _ ≤ (3 / (4 * (j : ℝ))) * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (3 * (m : ℝ) / 4) / (j : ℝ) := by ring
  calc
    _ ≤ (1 / (n + 2 : ℝ)) ^ (2 * m) / low ^ (2 * m) :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hlow _) hlowEig
    _ = ((1 / (n + 2 : ℝ)) / low) ^ (2 * m) := (div_pow _ _ _).symm
    _ ≤ ((3 * (m : ℝ) / 4) / (j : ℝ)) ^ (2 * m) :=
      pow_le_pow_left₀ (by positivity) hbase _
    _ = (3 * (m : ℝ) / 4) ^ (2 * m) * ((j : ℝ) ^ (2 * m))⁻¹ := by
      rw [div_pow, div_eq_mul_inv]

theorem eigenvalue_eventual_reciprocal_tail_bound (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ,
      2 ≤ j → j ≤ n →
        (1 / (n + 2 : ℝ)) ^ (2 * m) / eigenvalue m n j ≤
          C * ((j : ℝ) ^ (2 * m))⁻¹ := by
  refine ⟨(3 * (m : ℝ) / 4) ^ (2 * m), ?_, 1, ?_⟩
  · apply pow_pos
    have hmr : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    positivity
  · intro n _ j hj hjn
    exact eigenvalue_reciprocal_tail_majorant m n j hm hj hjn

#print axioms eigenvalue_circulant_interlacing
#print axioms eigenvalue_circulant_power_bounds
#print axioms eigenvalue_circulant_lower_bound
#print axioms eigenvalue_fixed_prefix_bound
#print axioms eigenvalue_reciprocal_tail_majorant
#print axioms eigenvalue_eventual_reciprocal_tail_bound

end MF21Restart
