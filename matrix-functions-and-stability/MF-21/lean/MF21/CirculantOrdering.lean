import MF21.CirculantSpectrum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Matrix Finset Polynomial
open scoped BigOperators
noncomputable section
namespace MF21Circulant

def foldedIndex {N : ℕ} (j : Fin N) : ℕ := (j.val + 1) / 2

def frequencyOrder {N : ℕ} (j : Fin N) : Fin N :=
  ⟨if j.val % 2 = 0 then j.val / 2 else N - (j.val + 1) / 2, by
    have := j.isLt
    split_ifs <;> omega⟩

theorem frequencyOrder_injective (N : ℕ) : Function.Injective (@frequencyOrder N) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp only [frequencyOrder] at hv
  have := i.isLt
  have := j.isLt
  split_ifs at hv <;> omega

def frequencyEquiv (N : ℕ) : Fin N ≃ Fin N :=
  Equiv.ofBijective frequencyOrder
    ⟨frequencyOrder_injective N, Finite.surjective_of_injective (frequencyOrder_injective N)⟩

theorem symbol_fold {N : ℕ} [NeZero N] (m : ℕ) (j : Fin N) :
    MF21Challenge.symbol m (2*Real.pi*(frequencyOrder j).val/N) =
      MF21Challenge.symbol m (2*Real.pi*(foldedIndex j)/N) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hj := j.isLt
  change MF21Challenge.symbol m (2*Real.pi*
    (if j.val % 2 = 0 then j.val / 2 else N - (j.val+1)/2 : ℕ)/N) =
      MF21Challenge.symbol m (2*Real.pi*((j.val+1)/2 : ℕ)/N)
  split_ifs with he
  · have h : j.val / 2 = (j.val + 1) / 2 := by omega
    rw [h]
  · have hsub : ((N - (j.val + 1) / 2 : ℕ) : ℝ) = N - ((j.val+1)/2 : ℕ) := by
      rw [Nat.cast_sub (by omega : (j.val+1)/2 ≤ N)]
    unfold MF21Challenge.symbol
    rw [hsub]
    have harg : 2*Real.pi*((N : ℝ)-((j.val+1)/2 : ℕ))/N/2 =
        Real.pi - (2*Real.pi*((j.val+1)/2 : ℕ)/N/2) := by field_simp
    rw [harg, Real.sin_pi_sub]

def orderedSymbol (m N : ℕ) (j : Fin N) : ℝ :=
  MF21Challenge.symbol m (2*Real.pi*(foldedIndex j)/N)

theorem orderedSymbol_monotone (m N : ℕ) [NeZero N] : Monotone (orderedSymbol m N) := by
  intro i j hij
  have hN : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hf : foldedIndex i ≤ foldedIndex j := by unfold foldedIndex; omega
  have hjhalf : (foldedIndex j : ℝ) ≤ N / 2 := by
    have h : 2 * foldedIndex j ≤ N := by unfold foldedIndex; have := j.isLt; omega
    have hh : (2 : ℝ) * (foldedIndex j : ℝ) ≤ N := by exact_mod_cast h
    linarith
  have hi0 : 0 ≤ 2*Real.pi*(foldedIndex i : ℝ)/N/2 := by positivity
  have hjtop : 2*Real.pi*(foldedIndex j : ℝ)/N/2 ≤ Real.pi/2 := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    apply (div_le_iff₀ hN).mpr
    nlinarith [Real.pi_pos]
  have hij' : 2*Real.pi*(foldedIndex i : ℝ)/N/2 ≤
      2*Real.pi*(foldedIndex j : ℝ)/N/2 := by gcongr
  have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ 2*Real.pi*(foldedIndex i : ℝ)/N/2 by linarith [Real.pi_pos]) hjtop hij'
  unfold orderedSymbol MF21Challenge.symbol
  apply pow_le_pow_left₀
  · have hh := Real.sin_nonneg_of_nonneg_of_le_pi hi0 (hij'.trans (by linarith [Real.pi_pos]))
    positivity
  · exact mul_le_mul_of_nonneg_left hsin (by norm_num)

theorem descendingEigenvalue_eq_of_charpoly {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (a : Fin n → ℝ) (ha : Antitone a)
    (hc : A.charpoly = ∏ i, (X - C (a i))) :
    MF21Challenge.descendingEigenvalue hA = a := by
  have hr : A.charpoly.roots = Multiset.map a univ.val := by
    rw [hc, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hs := hA.sort_roots_charpoly_eq_eigenvalues₀
  rw [hr] at hs
  simp only [Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
    Function.comp_def, RCLike.re_to_real, Multiset.coe_sort] at hs
  rw [List.mergeSort_of_pairwise (by
    simpa only [decide_eq_true_eq, ← List.sortedGE_iff_pairwise] using ha.sortedGE_ofFn)] at hs
  rw [List.ofFn_congr (Fintype.card_fin n) hA.eigenvalues₀] at hs
  exact (List.ofFn_injective hs).symm

theorem realCirculant_ordered_charpoly (m N : ℕ) [NeZero N] :
    (realCirculant (N := N) m).charpoly = ∏ j : Fin N, (X - C (orderedSymbol m N j)) := by
  rw [realCirculant_charpoly]
  have hp := (frequencyEquiv N).prod_comp
    (fun l : Fin N ↦ X - C (MF21Challenge.symbol m (2*Real.pi*l.val/N)))
  rw [← hp]
  apply prod_congr rfl
  intro j _
  change (X - C (MF21Challenge.symbol m (2*Real.pi*(frequencyOrder j).val/N))) = _
  rw [symbol_fold]
  rfl

theorem realCirculant_descending_eigenvalue (m N : ℕ) [NeZero N] (j : Fin N) :
    MF21Challenge.descendingEigenvalue (realCirculant_isHermitian m) j =
      orderedSymbol m N j.rev := by
  have ha : Antitone (fun j : Fin N ↦ orderedSymbol m N j.rev) :=
    fun i j hij ↦ orderedSymbol_monotone m N (Fin.rev_le_rev.mpr hij)
  have hc : (realCirculant (N := N) m).charpoly =
      ∏ j : Fin N, (X - C (orderedSymbol m N j.rev)) := by
    rw [realCirculant_ordered_charpoly]
    exact (Equiv.prod_comp Fin.revPerm (fun j : Fin N ↦ X - C (orderedSymbol m N j))).symm
  exact congrFun (descendingEigenvalue_eq_of_charpoly (realCirculant_isHermitian m) _ ha hc) j

/-- Both sides of the exact circulant comparison, indexed increasingly.
The source index is `j.val+1`, so `foldedIndex` is exactly its floor after division by 2. -/
theorem toeplitz_circulant_interlacing (m n N : ℕ) [NeZero N]
    (hN : n + 2*m ≤ N) (j : Fin n) :
    orderedSymbol m N ⟨j.val, by omega⟩ ≤ MF21Challenge.eigenvalue m n j ∧
    MF21Challenge.eigenvalue m n j ≤ orderedSymbol m N ⟨N - n + j.val, by omega⟩ := by
  have hnN : n ≤ N := by omega
  let f := Fin.castLE hnN
  have hf : Function.Injective f := Fin.castLE_injective hnN
  have hcomp := MF21Challenge.coordinateEmbedding_compression f (realCirculant (N := N) m)
  rw [realCirculant_principal m n hN] at hcomp
  have h := MF21Challenge.compression_interlacing (realCirculant (N := N) m)
    (MF21Challenge.toeplitz m n) (realCirculant_isHermitian m)
    (MF21Challenge.toeplitz_isHermitian m n)
    (MF21Challenge.coordinateEmbedding f) (MF21Challenge.coordinateEmbedding_isometry f hf)
    hcomp hnN j.rev.val j.rev.isLt
  rw [realCirculant_descending_eigenvalue, realCirculant_descending_eigenvalue] at h
  have hleft : (⟨N - n + j.rev.val, by omega⟩ : Fin N).rev = ⟨j.val, by omega⟩ := by
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  have hright : (⟨j.rev.val, j.rev.isLt.trans_le hnN⟩ : Fin N).rev =
      ⟨N - n + j.val, by omega⟩ := by
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  rw [hleft, hright] at h
  exact h

end MF21Circulant

#print axioms MF21Circulant.frequencyOrder_injective
#print axioms MF21Circulant.orderedSymbol_monotone
#print axioms MF21Circulant.descendingEigenvalue_eq_of_charpoly
#print axioms MF21Circulant.realCirculant_descending_eigenvalue
#print axioms MF21Circulant.toeplitz_circulant_interlacing
