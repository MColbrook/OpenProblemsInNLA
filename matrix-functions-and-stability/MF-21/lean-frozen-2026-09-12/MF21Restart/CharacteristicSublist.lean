import MF21Restart.NormalizedBoundary

set_option autoImplicit false
noncomputable section

namespace MF21Restart

theorem characteristicRoots_eq_implies_index_eq_or_oscillatory
    (m : ℕ) (hm : 2 ≤ m) (θ : ℝ) (hθ : 0 < θ) (hθπ : θ ≤ Real.pi)
    (a b : Fin (2 * m)) (hab : characteristicRoots m θ a = characteristicRoots m θ b) :
    a = b ∨ (a.val = m - 1 ∧ b.val = m) ∨ (a.val = m ∧ b.val = m - 1) := by
  have ha_bound := a.isLt
  have hb_bound := b.isLt
  have hnorm := congrArg norm hab
  have ha_regions := characteristicRoots_norm_regions m hm θ hθ hθπ a
  have hb_regions := characteristicRoots_norm_regions m hm θ hθ hθπ b
  have hleft_iff : a.val < m - 1 ↔ b.val < m - 1 := by
    rw [← ha_regions.1, ← hb_regions.1, hnorm]
  have hout_iff : m < a.val ↔ m < b.val := by
    rw [← ha_regions.2, ← hb_regions.2, hnorm]
  by_cases ha : a.val < m - 1
  · have hb : b.val < m - 1 := hleft_iff.mp ha
    rw [characteristicRoots_stable m θ a ha, characteristicRoots_stable m θ b hb] at hab
    have hidx :
        (⟨a.val + 1, ⟨by omega, by omega⟩⟩ : {ell : ℕ // 1 ≤ ell ∧ ell < m}) =
          ⟨b.val + 1, ⟨by omega, by omega⟩⟩ :=
      stableRootCurve_rootKappa_injective m θ hθ hθπ hab
    have hval := congrArg Subtype.val hidx
    change a.val + 1 = b.val + 1 at hval
    exact Or.inl (Fin.ext (by omega))
  · by_cases haout : m < a.val
    · have hbout : m < b.val := hout_iff.mp haout
      rw [characteristicRoots_exterior m θ a haout,
        characteristicRoots_exterior m θ b hbout] at hab
      have hroot : stableRootCurve (rootKappa m (a.val - m)) θ =
          stableRootCurve (rootKappa m (b.val - m)) θ := inv_inj.mp hab
      have hidx :
          (⟨a.val - m, ⟨by omega, by omega⟩⟩ : {ell : ℕ // 1 ≤ ell ∧ ell < m}) =
            ⟨b.val - m, ⟨by omega, by omega⟩⟩ :=
        stableRootCurve_rootKappa_injective m θ hθ hθπ hroot
      have hval := congrArg Subtype.val hidx
      change a.val - m = b.val - m at hval
      exact Or.inl (Fin.ext (by omega))
    · have hb : ¬b.val < m - 1 := fun h => ha (hleft_iff.mpr h)
      have hbout : ¬m < b.val := fun h => haout (hout_iff.mpr h)
      by_cases heq : a.val = b.val
      · exact Or.inl (Fin.ext heq)
      · right
        omega

theorem characteristicRoots_sublist_injective (m k : ℕ) (hm : 2 ≤ m)
    (u : Fin k → Fin (2 * m)) (hu : Function.Injective u)
    (hsep : ∀ i j, ¬((u i).val = m - 1 ∧ (u j).val = m))
    (θ : ℝ) (hθ : 0 < θ) (hθπ : θ ≤ Real.pi) :
    Function.Injective (fun i => characteristicRoots m θ (u i)) := by
  intro a b hab
  rcases characteristicRoots_eq_implies_index_eq_or_oscillatory m hm θ hθ hθπ
      (u a) (u b) hab with h | h | h
  · exact hu h
  · exact False.elim (hsep a b h)
  · exact False.elim (hsep b a ⟨h.2, h.1⟩)

theorem normalizedRootVandermonde_ne_zero_on_Icc (m k : ℕ) (hm : 2 ≤ m)
    (u : Fin k → Fin (2 * m)) (hu : Function.Injective u)
    (hsep : ∀ i j, ¬((u i).val = m - 1 ∧ (u j).val = m))
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi) :
    normalizedRootVandermonde m k u θ ≠ 0 := by
  by_cases hzero : θ = 0
  · subst θ
    exact normalizedRootVandermonde_zero_ne_zero m k hm u hu
  · have hpos : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hzero)
    have hdet := Matrix.det_vandermonde_ne_zero_iff.mpr
      (characteristicRoots_sublist_injective m k hm u hu hsep θ hpos hθ.2)
    rw [rootVandermonde_eq_pow_mul_normalized] at hdet
    exact (mul_ne_zero_iff.mp hdet).2

theorem normalizedBoundaryCoefficient_ne_zero_on_Icc (m : ℕ) (hm : 2 ≤ m)
    (s : Finset (Fin (2 * m))) (hs : s.card = m)
    (hsep : ∀ a b : Fin (2 * m), a.val = m - 1 → b.val = m → (a ∈ s ↔ b ∉ s))
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi) :
    normalizedBoundaryCoefficient m s hs θ ≠ 0 := by
  have hsign : (↑↑(boundaryLaplaceSign m s hs) : ℂ) ≠ 0 := by
    rcases Int.units_eq_one_or (boundaryLaplaceSign m s hs) with h | h <;> simp [h]
  apply mul_ne_zero
  · apply mul_ne_zero hsign
    apply normalizedRootVandermonde_ne_zero_on_Icc m m hm _
      (sᶜ.orderEmbOfFin (boundary_compl_card hs)).injective ?_ θ hθ
    intro i j hij
    have hi : sᶜ.orderEmbOfFin (boundary_compl_card hs) i ∉ s :=
      Finset.mem_compl.mp (sᶜ.orderEmbOfFin_mem (boundary_compl_card hs) i)
    have hj : sᶜ.orderEmbOfFin (boundary_compl_card hs) j ∉ s :=
      Finset.mem_compl.mp (sᶜ.orderEmbOfFin_mem (boundary_compl_card hs) j)
    exact hi ((hsep _ _ hij.1 hij.2).mpr hj)
  · apply normalizedRootVandermonde_ne_zero_on_Icc m m hm _
      (s.orderEmbOfFin hs).injective ?_ θ hθ
    intro i j hij
    exact ((hsep _ _ hij.1 hij.2).mp (s.orderEmbOfFin_mem hs i))
      (s.orderEmbOfFin_mem hs j)

#print axioms characteristicRoots_eq_implies_index_eq_or_oscillatory
#print axioms characteristicRoots_sublist_injective
#print axioms normalizedRootVandermonde_ne_zero_on_Icc
#print axioms normalizedBoundaryCoefficient_ne_zero_on_Icc

end MF21Restart
