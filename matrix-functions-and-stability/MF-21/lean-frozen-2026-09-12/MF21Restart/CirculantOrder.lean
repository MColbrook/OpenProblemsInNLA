import MF21Restart.CirculantSpectrum
import MF21Restart.SpectralOrder
import Mathlib.Data.List.FinRange

/-!
The complete increasing spectrum of the actual Fourier circulant.
The frequency permutation retains both members of each conjugate pair,
with the single pi frequency occurring only when the size is even.
See the prior lock `CIRCULANT_ORDER_STATEMENTS.md`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

def circulantOrderedValue (m N j : ℕ) : ℝ :=
  symbol m (2 * Real.pi * ((j / 2 : ℕ) : ℝ) / (N : ℝ))

private def pairedFrequencyNat (N i : ℕ) : ℕ :=
  if i = 0 then 0 else if i % 2 = 1 then (i + 1) / 2 else N - i / 2

private theorem pairedFrequencyNat_lt (N : ℕ) (i : Fin N) :
    pairedFrequencyNat N i.val < N := by
  have hi := i.isLt
  unfold pairedFrequencyNat
  split_ifs <;> omega

private def pairedFrequency (N : ℕ) (i : Fin N) : Fin N :=
  ⟨pairedFrequencyNat N i.val, pairedFrequencyNat_lt N i⟩

private theorem pairedFrequency_injective (N : ℕ) :
    Function.Injective (pairedFrequency N) := by
  intro a b hab
  have ha := a.isLt
  have hb := b.isLt
  have heq := congrArg Fin.val hab
  change pairedFrequencyNat N a.val = pairedFrequencyNat N b.val at heq
  apply Fin.ext
  unfold pairedFrequencyNat at heq
  split_ifs at heq <;> omega

private def pairedFrequencyEquiv (N : ℕ) : Fin N ≃ Fin N :=
  Equiv.ofBijective (pairedFrequency N)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨pairedFrequency_injective N, rfl⟩)

private theorem symbol_pairedFrequency (m N : ℕ) (i : Fin N) :
    symbol m (2 * Real.pi * ((pairedFrequencyEquiv N i).val : ℝ) / (N : ℝ)) =
      circulantOrderedValue m N (i.val + 1) := by
  have hi := i.isLt
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  change symbol m (2 * Real.pi * (pairedFrequencyNat N i.val : ℝ) / (N : ℝ)) = _
  by_cases hi0 : i.val = 0
  · simp [pairedFrequencyNat, hi0, circulantOrderedValue]
  by_cases hodd : i.val % 2 = 1
  · simp only [pairedFrequencyNat, if_neg hi0, if_pos hodd, circulantOrderedValue]
  have hhalf : (i.val + 1) / 2 = i.val / 2 := by omega
  have hhalfN : i.val / 2 ≤ N := by omega
  simp only [pairedFrequencyNat, if_neg hi0, if_neg hodd,
    circulantOrderedValue, hhalf, Nat.cast_sub hhalfN]
  have hangle : 2 * Real.pi * ((N : ℝ) - (i.val / 2 : ℕ)) / (N : ℝ) =
      2 * Real.pi - 2 * Real.pi * ((i.val / 2 : ℕ) : ℝ) / (N : ℝ) := by
    field_simp [hN]
    <;> ring
  rw [hangle, symbol_eq_cosine_power, symbol_eq_cosine_power, Real.cos_two_pi_sub]

theorem fourierCirculant_charpoly_real (m N : ℕ) (hmN : m < N) :
    (fourierCirculant m N).charpoly =
      ∏ ell : Fin N, (Polynomial.X - Polynomial.C
        (symbol m (2 * Real.pi * (ell.val : ℝ) / (N : ℝ)))) := by
  apply Polynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
  rw [← Matrix.charpoly_map]
  have hhom : (Complex.ofRealHom : ℝ → ℂ) = Complex.ofReal := rfl
  simpa only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, hhom, Complex.ofRealHom_eq_coe] using
      fourierCirculant_charpoly_complex m N hmN

theorem fourierCirculant_charpoly_ordered (m N : ℕ) (hmN : m < N) :
    (fourierCirculant m N).charpoly =
      ∏ i : Fin N, (Polynomial.X - Polynomial.C
        (circulantOrderedValue m N (i.val + 1))) := by
  rw [fourierCirculant_charpoly_real m N hmN]
  calc
    (∏ ell : Fin N, (Polynomial.X - Polynomial.C
        (symbol m (2 * Real.pi * (ell.val : ℝ) / (N : ℝ))))) =
        ∏ i : Fin N, (Polynomial.X - Polynomial.C
          (symbol m (2 * Real.pi * ((pairedFrequencyEquiv N i).val : ℝ) / (N : ℝ)))) :=
      (Equiv.prod_comp (pairedFrequencyEquiv N) _).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      rw [symbol_pairedFrequency]

private theorem circulant_frequency_mem (N : ℕ) (i : Fin N) :
    2 * Real.pi * (((i.val + 1) / 2 : ℕ) : ℝ) / (N : ℝ) ∈ Set.Icc 0 Real.pi := by
  have hi := i.isLt
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hdouble : (2 : ℝ) * (((i.val + 1) / 2 : ℕ) : ℝ) ≤ N := by
    exact_mod_cast (show 2 * ((i.val + 1) / 2) ≤ N by omega)
  constructor
  · positivity
  · apply (div_le_iff₀ hN).mpr
    nlinarith [Real.pi_pos]

theorem circulantOrderedValue_monotone (m N : ℕ) (hm : 1 ≤ m) :
    Monotone (fun i : Fin N => circulantOrderedValue m N (i.val + 1)) := by
  intro i j hij
  apply (symbol_strictMonoOn m hm).monotoneOn
    (circulant_frequency_mem N i) (circulant_frequency_mem N j)
  have hhalf : (((i.val + 1) / 2 : ℕ) : ℝ) ≤ (((j.val + 1) / 2 : ℕ) : ℝ) := by
    exact_mod_cast (show (i.val + 1) / 2 ≤ (j.val + 1) / 2 by
      have hij' : i.val ≤ j.val := hij
      omega)
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hhalf (by positivity)) (by positivity)

/-- This is equality of the increasing lists with multiplicities, rather
than equality of the sets of distinct eigenvalues. -/
theorem fourierCirculant_sorted_eigenvalues (m N : ℕ) (hm : 1 ≤ m) (hmN : m < N) :
    Multiset.sort (Multiset.ofList
      (List.ofFn (fourierCirculant_isHermitian m N hmN).eigenvalues)) =
      List.ofFn (fun i : Fin N => circulantOrderedValue m N (i.val + 1)) := by
  have hroots : (fourierCirculant m N).charpoly.roots =
      (List.ofFn (fun i : Fin N => circulantOrderedValue m N (i.val + 1)) : Multiset ℝ) := by
    rw [fourierCirculant_charpoly_ordered m N hmN, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hraw : Multiset.ofList
      (List.ofFn (fourierCirculant_isHermitian m N hmN).eigenvalues) =
      (fourierCirculant m N).charpoly.roots := by
    rw [(fourierCirculant_isHermitian m N hmN).roots_charpoly_eq_eigenvalues]
    simp [Function.comp_def]
  rw [hraw, hroots, Multiset.coe_sort]
  exact List.mergeSort_eq_self _ (circulantOrderedValue_monotone m N hm).sortedLE_ofFn.pairwise

#print axioms fourierCirculant_charpoly_real
#print axioms fourierCirculant_charpoly_ordered
#print axioms circulantOrderedValue_monotone
#print axioms fourierCirculant_sorted_eigenvalues

end MF21Restart
