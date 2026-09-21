import MF21Restart.FourierRecurrence

/-!
The normalized Fourier recurrence at a single natural index is equivalent
to the full shifted Fourier equation. This is a concrete coefficient
identity, with no solution or geometric-representation hypothesis.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

/-- Solve the full Fourier equation for its terminal value, using the
proved nonzero endpoint coefficient. Both directions hold for any sequence. -/
theorem fourierRecurrence_equation_iff
    (m : ℕ) (hm : 1 ≤ m) (lam : ℂ) (u : ℕ → ℂ) (k : ℕ) :
    (u (k + 2 * m) =
      ∑ i : Fin (2 * m),
        (fourierRecurrence m lam).coeffs i * u (k + i.val)) ↔
    (∑ t : Fin (2 * m + 1),
      (fourierCoeff m ((t.val : ℤ) - (m : ℤ)) : ℂ) * u (k + t.val)) =
      lam * u (k + m) := by
  classical
  have ha : (fourierCoeff m (m : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast fourierCoeff_right_endpoint_ne_zero m
  have hend : ((2 * m : ℕ) : ℤ) - (m : ℤ) = (m : ℤ) := by omega
  have hsplit :
      (∑ t : Fin (2 * m + 1),
        (fourierCoeff m ((t.val : ℤ) - (m : ℤ)) : ℂ) * u (k + t.val)) =
      (∑ i : Fin (2 * m),
        (fourierCoeff m ((i.val : ℤ) - (m : ℤ)) : ℂ) * u (k + i.val)) +
        (fourierCoeff m (m : ℤ) : ℂ) * u (k + 2 * m) := by
    rw [Fin.sum_univ_castSucc]
    change
      (∑ i : Fin (2 * m),
        (fourierCoeff m ((i.val : ℤ) - (m : ℤ)) : ℂ) * u (k + i.val)) +
          (fourierCoeff m (((2 * m : ℕ) : ℤ) - (m : ℤ)) : ℂ) *
            u (k + 2 * m) = _
    rw [hend]
  have hmindex : m < 2 * m := by omega
  let mid : Fin (2 * m) := ⟨m, hmindex⟩
  have hmiddle :
      (∑ i : Fin (2 * m),
        (if i.val = m then lam else 0) * u (k + i.val)) =
        lam * u (k + m) := by
    rw [Finset.sum_eq_single mid]
    · simp [mid]
    · intro i _ hi
      have him : i.val ≠ m := by
        intro h
        apply hi
        apply Fin.ext
        exact h
      simp [him]
    · simp
  have hnormalized :
      (∑ i : Fin (2 * m),
        (fourierRecurrence m lam).coeffs i * u (k + i.val)) =
        (lam * u (k + m) - ∑ i : Fin (2 * m),
          (fourierCoeff m ((i.val : ℤ) - (m : ℤ)) : ℂ) * u (k + i.val)) /
          (fourierCoeff m (m : ℤ) : ℂ) := by
    change
      (∑ i : Fin (2 * m),
        ((if i.val = m then lam else 0) -
          (fourierCoeff m ((i.val : ℤ) - (m : ℤ)) : ℂ)) /
            (fourierCoeff m (m : ℤ) : ℂ) * u (k + i.val)) = _
    simp_rw [div_mul_eq_mul_div₀, sub_mul]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, hmiddle]
  rw [hnormalized, hsplit, eq_div_iff ha]
  constructor
  · intro h
    have hsum := (eq_sub_iff_add_eq).mp h
    calc
      (∑ i : Fin (2 * m),
        (fourierCoeff m ((i.val : ℤ) - (m : ℤ)) : ℂ) * u (k + i.val)) +
          (fourierCoeff m (m : ℤ) : ℂ) * u (k + 2 * m) =
        u (k + 2 * m) * (fourierCoeff m (m : ℤ) : ℂ) +
          (∑ i : Fin (2 * m),
            (fourierCoeff m ((i.val : ℤ) - (m : ℤ)) : ℂ) * u (k + i.val)) := by ring
      _ = lam * u (k + m) := hsum
  · intro h
    apply (eq_sub_iff_add_eq).mpr
    calc
      u (k + 2 * m) * (fourierCoeff m (m : ℤ) : ℂ) +
          (∑ i : Fin (2 * m),
            (fourierCoeff m ((i.val : ℤ) - (m : ℤ)) : ℂ) * u (k + i.val)) =
        (∑ i : Fin (2 * m),
          (fourierCoeff m ((i.val : ℤ) - (m : ℤ)) : ℂ) * u (k + i.val)) +
            (fourierCoeff m (m : ℤ) : ℂ) * u (k + 2 * m) := by ring
      _ = lam * u (k + m) := h

#print axioms fourierRecurrence_equation_iff

end MF21Restart
