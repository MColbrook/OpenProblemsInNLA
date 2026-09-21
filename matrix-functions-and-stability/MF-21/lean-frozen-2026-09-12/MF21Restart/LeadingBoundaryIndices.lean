import MF21Restart.BoundaryProductDecay

/-!
The exact inherited orders and Laplace signs of the two actual leading
subsets. With the frozen root order, Sminus preserves the block order and
Splus exchanges the adjacent oscillatory columns. Thus their signs are
respectively +1 and -1, fixing the manuscript's unspecified sign in (15).

The statement lock is `LEADING_BOUNDARY_INDICES_STATEMENTS.md`.
-/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

@[simp]
lemma mem_boundaryLeadingZIndices_iff (m : ℕ) (hm : 1 ≤ m) (i : Fin (2 * m)) :
    i ∈ boundaryLeadingZIndices m hm ↔ i.val = m - 1 ∨ m < i.val := by
  simp only [boundaryLeadingZIndices, Finset.mem_insert, mem_boundaryExteriorIndices,
    Fin.ext_iff]

@[simp]
lemma mem_boundaryLeadingZInvIndices_iff (m : ℕ) (hm : 1 ≤ m) (i : Fin (2 * m)) :
    i ∈ boundaryLeadingZInvIndices m hm ↔ m ≤ i.val := by
  simp only [boundaryLeadingZInvIndices, Finset.mem_insert, mem_boundaryExteriorIndices,
    Fin.ext_iff]
  omega

theorem card_boundaryLeadingZInvIndices (m : ℕ) (hm : 1 ≤ m) :
    (boundaryLeadingZInvIndices m hm).card = m := by
  have hn : (⟨m, by omega⟩ : Fin (2 * m)) ∉ boundaryExteriorIndices m := by
    simp only [mem_boundaryExteriorIndices, lt_self_iff_false, not_false_eq_true]
  rw [boundaryLeadingZInvIndices, Finset.card_insert_of_notMem hn,
    card_boundaryExteriorIndices m hm]
  omega

theorem boundaryLeadingZInvIndices_orderEmb_val (m : ℕ) (hm : 1 ≤ m) (i : Fin m) :
    ((boundaryLeadingZInvIndices m hm).orderEmbOfFin
      (card_boundaryLeadingZInvIndices m hm) i).val = m + i.val := by
  let f : Fin m → Fin (2 * m) := fun j => ⟨m + j.val, by have := j.isLt; omega⟩
  have hfmem : ∀ j, f j ∈ boundaryLeadingZInvIndices m hm := by
    intro j
    rw [mem_boundaryLeadingZInvIndices_iff]
    change m ≤ m + j.val
    omega
  have hfmono : StrictMono f := by
    intro j k hjk
    change m + j.val < m + k.val
    exact Nat.add_lt_add_left hjk m
  have henum := Finset.orderEmbOfFin_unique
    (card_boundaryLeadingZInvIndices m hm) hfmem hfmono
  simpa only [f] using
    congrArg (fun g : Fin m → Fin (2 * m) => (g i).val) henum.symm

theorem boundaryLeadingZInvIndices_compl_orderEmb_val
    (m : ℕ) (hm : 1 ≤ m) (i : Fin m) :
    ((boundaryLeadingZInvIndices m hm)ᶜ.orderEmbOfFin
      (boundary_compl_card (card_boundaryLeadingZInvIndices m hm)) i).val = i.val := by
  let f : Fin m → Fin (2 * m) := fun j => ⟨j.val, by have := j.isLt; omega⟩
  have hfmem : ∀ j, f j ∈ (boundaryLeadingZInvIndices m hm)ᶜ := by
    intro j
    rw [Finset.mem_compl, mem_boundaryLeadingZInvIndices_iff]
    change ¬m ≤ j.val
    exact not_le_of_gt j.isLt
  have hfmono : StrictMono f := by
    intro j k hjk
    exact hjk
  have henum := Finset.orderEmbOfFin_unique
    (boundary_compl_card (card_boundaryLeadingZInvIndices m hm)) hfmem hfmono
  simpa only [f] using
    congrArg (fun g : Fin m → Fin (2 * m) => (g i).val) henum.symm

theorem boundaryLeadingZIndices_orderEmb_val (m : ℕ) (hm : 1 ≤ m) (i : Fin m) :
    ((boundaryLeadingZIndices m hm).orderEmbOfFin
      (card_boundaryLeadingZIndices m hm) i).val =
        if i.val = 0 then m - 1 else m + i.val := by
  let f : Fin m → Fin (2 * m) := fun j =>
    ⟨if j.val = 0 then m - 1 else m + j.val, by
      have := j.isLt
      split_ifs <;> omega⟩
  have hfmem : ∀ j, f j ∈ boundaryLeadingZIndices m hm := by
    intro j
    rw [mem_boundaryLeadingZIndices_iff]
    change (if j.val = 0 then m - 1 else m + j.val) = m - 1 ∨
      m < (if j.val = 0 then m - 1 else m + j.val)
    split_ifs <;> omega
  have hfmono : StrictMono f := by
    intro j k hjk
    have hj := j.isLt
    have hk := k.isLt
    change j.val < k.val at hjk
    change (if j.val = 0 then m - 1 else m + j.val) <
      (if k.val = 0 then m - 1 else m + k.val)
    split_ifs <;> omega
  have henum := Finset.orderEmbOfFin_unique
    (card_boundaryLeadingZIndices m hm) hfmem hfmono
  simpa only [f] using
    congrArg (fun g : Fin m → Fin (2 * m) => (g i).val) henum.symm

theorem boundaryLeadingZIndices_compl_orderEmb_val
    (m : ℕ) (hm : 1 ≤ m) (i : Fin m) :
    ((boundaryLeadingZIndices m hm)ᶜ.orderEmbOfFin
      (boundary_compl_card (card_boundaryLeadingZIndices m hm)) i).val =
        if i.val = m - 1 then m else i.val := by
  let f : Fin m → Fin (2 * m) := fun j =>
    ⟨if j.val = m - 1 then m else j.val, by
      have := j.isLt
      split_ifs <;> omega⟩
  have hfmem : ∀ j, f j ∈ (boundaryLeadingZIndices m hm)ᶜ := by
    intro j
    rw [Finset.mem_compl, mem_boundaryLeadingZIndices_iff]
    have hj := j.isLt
    change ¬((if j.val = m - 1 then m else j.val) = m - 1 ∨
      m < (if j.val = m - 1 then m else j.val))
    split_ifs <;> omega
  have hfmono : StrictMono f := by
    intro j k hjk
    have hj := j.isLt
    have hk := k.isLt
    change j.val < k.val at hjk
    change (if j.val = m - 1 then m else j.val) <
      (if k.val = m - 1 then m else k.val)
    split_ifs <;> omega
  have henum := Finset.orderEmbOfFin_unique
    (boundary_compl_card (card_boundaryLeadingZIndices m hm)) hfmem hfmono
  simpa only [f] using
    congrArg (fun g : Fin m → Fin (2 * m) => (g i).val) henum.symm

theorem boundaryColumnEquiv_leadingZInv (m : ℕ) (hm : 1 ≤ m) :
    boundaryColumnEquiv m (boundaryLeadingZInvIndices m hm)
      (card_boundaryLeadingZInvIndices m hm) = boundaryRowEquiv m := by
  apply Equiv.ext
  intro x
  rcases x with i | i
  · apply Fin.ext
    simpa only [boundaryColumnEquiv_inl, boundaryRowEquiv_inl_val] using
      boundaryLeadingZInvIndices_compl_orderEmb_val m hm i
  · apply Fin.ext
    simpa only [boundaryColumnEquiv_inr, boundaryRowEquiv_inr_val] using
      boundaryLeadingZInvIndices_orderEmb_val m hm i

theorem boundaryColumnEquiv_leadingZ (m : ℕ) (hm : 1 ≤ m) :
    boundaryColumnEquiv m (boundaryLeadingZIndices m hm)
      (card_boundaryLeadingZIndices m hm) =
      (boundaryRowEquiv m).trans
        (Equiv.swap (⟨m - 1, by omega⟩ : Fin (2 * m)) ⟨m, by omega⟩) := by
  let a : Fin (2 * m) := ⟨m - 1, by omega⟩
  let b : Fin (2 * m) := ⟨m, by omega⟩
  change boundaryColumnEquiv m (boundaryLeadingZIndices m hm)
    (card_boundaryLeadingZIndices m hm) = (boundaryRowEquiv m).trans (Equiv.swap a b)
  apply Equiv.ext
  intro x
  rcases x with i | i
  · change ((boundaryLeadingZIndices m hm)ᶜ.orderEmbOfFin
      (boundary_compl_card (card_boundaryLeadingZIndices m hm)) i) =
      Equiv.swap a b (boundaryRowEquiv m (Sum.inl i))
    by_cases hi : i.val = m - 1
    · have hr : boundaryRowEquiv m (Sum.inl i) = a := by
        apply Fin.ext
        exact hi
      rw [hr, Equiv.swap_apply_left]
      apply Fin.ext
      simpa only [if_pos hi] using boundaryLeadingZIndices_compl_orderEmb_val m hm i
    · have hna : boundaryRowEquiv m (Sum.inl i) ≠ a := by
        intro h
        exact hi (congrArg Fin.val h)
      have hnb : boundaryRowEquiv m (Sum.inl i) ≠ b := by
        intro h
        have hv : i.val = m := congrArg Fin.val h
        have := i.isLt
        omega
      rw [Equiv.swap_apply_of_ne_of_ne hna hnb]
      apply Fin.ext
      simpa only [if_neg hi, boundaryRowEquiv_inl_val] using
        boundaryLeadingZIndices_compl_orderEmb_val m hm i
  · change ((boundaryLeadingZIndices m hm).orderEmbOfFin
      (card_boundaryLeadingZIndices m hm) i) =
      Equiv.swap a b (boundaryRowEquiv m (Sum.inr i))
    by_cases hi : i.val = 0
    · have hr : boundaryRowEquiv m (Sum.inr i) = b := by
        apply Fin.ext
        change m + i.val = m
        omega
      rw [hr, Equiv.swap_apply_right]
      apply Fin.ext
      simpa only [if_pos hi] using boundaryLeadingZIndices_orderEmb_val m hm i
    · have hna : boundaryRowEquiv m (Sum.inr i) ≠ a := by
        intro h
        have hv : m + i.val = m - 1 := congrArg Fin.val h
        omega
      have hnb : boundaryRowEquiv m (Sum.inr i) ≠ b := by
        intro h
        have hv : m + i.val = m := congrArg Fin.val h
        omega
      rw [Equiv.swap_apply_of_ne_of_ne hna hnb]
      apply Fin.ext
      simpa only [if_neg hi, boundaryRowEquiv_inr_val] using
        boundaryLeadingZIndices_orderEmb_val m hm i

theorem boundaryLaplaceSign_leadingZInv (m : ℕ) (hm : 1 ≤ m) :
    boundaryLaplaceSign m (boundaryLeadingZInvIndices m hm)
      (card_boundaryLeadingZInvIndices m hm) = 1 := by
  simp only [boundaryLaplaceSign, boundaryColumnEquiv_leadingZInv,
    Equiv.symm_trans_self, Equiv.Perm.sign_refl]

theorem boundaryLaplaceSign_leadingZ (m : ℕ) (hm : 1 ≤ m) :
    boundaryLaplaceSign m (boundaryLeadingZIndices m hm)
      (card_boundaryLeadingZIndices m hm) = -1 := by
  let a : Fin (2 * m) := ⟨m - 1, by omega⟩
  let b : Fin (2 * m) := ⟨m, by omega⟩
  have hab : a ≠ b := by
    intro h
    have hv : m - 1 = m := congrArg Fin.val h
    omega
  have hcol : boundaryColumnEquiv m (boundaryLeadingZIndices m hm)
      (card_boundaryLeadingZIndices m hm) = (boundaryRowEquiv m).trans (Equiv.swap a b) :=
    boundaryColumnEquiv_leadingZ m hm
  simpa only [boundaryLaplaceSign, hcol, Equiv.symm_trans, Equiv.trans_assoc,
    Equiv.symm_trans_self, Equiv.trans_refl, Equiv.symm_swap] using
      (Equiv.Perm.sign_swap hab)

#print axioms card_boundaryLeadingZInvIndices
#print axioms boundaryLeadingZInvIndices_orderEmb_val
#print axioms boundaryLeadingZInvIndices_compl_orderEmb_val
#print axioms boundaryLeadingZIndices_orderEmb_val
#print axioms boundaryLeadingZIndices_compl_orderEmb_val
#print axioms boundaryLaplaceSign_leadingZInv
#print axioms boundaryLaplaceSign_leadingZ

end MF21Restart
