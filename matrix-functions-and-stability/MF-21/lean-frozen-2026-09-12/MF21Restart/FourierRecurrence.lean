import MF21Restart.FourierLaurent
import MF21Restart.FourierEndpoint
import Mathlib.Algebra.LinearRecurrence
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field

/-!
The actual normalized recurrence of the MF-21 Fourier stencil. Multiplying
the proved Laurent identity by z^m produces a polynomial of degree 2m.
Its terminal coefficient is the proved nonzero Fourier endpoint, allowing
the eigenvalue equation to be put in Mathlib's LinearRecurrence convention.
The finite Toeplitz and boundary-kernel correspondence is not proved here.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

/-- The natural-power polynomial obtained by shifting the actual Fourier
support interval [-m,m] to [0,2m]. -/
theorem fourierCoeff_shifted_laurent_sum
    (m : ℕ) (z : ℂ) (hz : z ≠ 0) :
    (∑ t : Fin (2 * m + 1),
      (fourierCoeff m ((t.val : ℤ) - (m : ℤ)) : ℂ) * z ^ t.val) =
      z ^ m * (2 - z - z⁻¹) ^ m := by
  classical
  have hshift :
      (∑ t : Fin (2 * m + 1),
        (fourierCoeff m ((t.val : ℤ) - (m : ℤ)) : ℂ) * z ^ t.val) =
      z ^ m * (∑ k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
        (fourierCoeff m k : ℂ) * z ^ k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun t _ => (t.val : ℤ) - (m : ℤ)) ?_ ?_ ?_ ?_
    · intro t _
      have ht := t.isLt
      apply Finset.mem_Icc.mpr
      constructor <;> omega
    · intro a _ b _ h
      apply Fin.ext
      change (a.val : ℤ) - (m : ℤ) = (b.val : ℤ) - (m : ℤ) at h
      omega
    · intro k hk
      have hk' := Finset.mem_Icc.mp hk
      let t : Fin (2 * m + 1) := ⟨(k + (m : ℤ)).toNat, by omega⟩
      refine ⟨t, Finset.mem_univ _, ?_⟩
      dsimp [t]
      omega
    · intro t _
      have he : (m : ℤ) + ((t.val : ℤ) - (m : ℤ)) = (t.val : ℤ) := by omega
      have hpow := zpow_add₀ hz (m : ℤ) ((t.val : ℤ) - (m : ℤ))
      rw [he, zpow_natCast, zpow_natCast] at hpow
      rw [hpow]
      ring
  rw [hshift, fourierCoeff_laurent_sum m z hz]

/-- The Fourier equation solved for its terminal value. The central
spectral term is at index m and the order is exactly 2m. -/
def fourierRecurrence (m : ℕ) (lam : ℂ) : LinearRecurrence ℂ where
  order := 2 * m
  coeffs i :=
    ((if i.val = m then lam else 0) -
      (fourierCoeff m ((i.val : ℤ) - (m : ℤ)) : ℂ)) /
      (fourierCoeff m (m : ℤ) : ℂ)

/-- A nonzero solution of the concrete Laurent spectral equation is a
characteristic root of the actual normalized Fourier recurrence. -/
theorem fourierRecurrence_charPoly_isRoot
    (m : ℕ) (hm : 1 ≤ m) (lam z : ℂ) (hz : z ≠ 0)
    (hvalue : (2 - z - z⁻¹) ^ m = lam) :
    (fourierRecurrence m lam).charPoly.IsRoot z := by
  classical
  have ha : (fourierCoeff m (m : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast fourierCoeff_right_endpoint_ne_zero m
  have hfull := fourierCoeff_shifted_laurent_sum m z hz
  rw [hvalue, Fin.sum_univ_castSucc] at hfull
  change
    (∑ i : Fin (2 * m),
      (fourierCoeff m ((i.val : ℤ) - (m : ℤ)) : ℂ) * z ^ i.val) +
        (fourierCoeff m (((2 * m : ℕ) : ℤ) - (m : ℤ)) : ℂ) * z ^ (2 * m) =
      z ^ m * lam at hfull
  have hend : ((2 * m : ℕ) : ℤ) - (m : ℤ) = (m : ℤ) := by omega
  rw [hend] at hfull
  have hmindex : m < 2 * m := by omega
  let mid : Fin (2 * m) := ⟨m, hmindex⟩
  have hmiddle :
      (∑ i : Fin (2 * m), (if i.val = m then lam else 0) * z ^ i.val) =
        lam * z ^ m := by
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
  have hrecSum :
      (∑ i : Fin (2 * m), (fourierRecurrence m lam).coeffs i * z ^ i.val) =
        (lam * z ^ m - ∑ i : Fin (2 * m),
          (fourierCoeff m ((i.val : ℤ) - (m : ℤ)) : ℂ) * z ^ i.val) /
          (fourierCoeff m (m : ℤ) : ℂ) := by
    change
      (∑ i : Fin (2 * m),
        ((if i.val = m then lam else 0) -
          (fourierCoeff m ((i.val : ℤ) - (m : ℤ)) : ℂ)) /
            (fourierCoeff m (m : ℤ) : ℂ) * z ^ i.val) = _
    simp_rw [div_mul_eq_mul_div₀, sub_mul]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, hmiddle]
  have hbase :
      z ^ (2 * m) =
        (lam * z ^ m - ∑ i : Fin (2 * m),
          (fourierCoeff m ((i.val : ℤ) - (m : ℤ)) : ℂ) * z ^ i.val) /
          (fourierCoeff m (m : ℤ) : ℂ) := by
    apply (eq_div_iff ha).2
    apply (eq_sub_iff_add_eq).2
    calc
      z ^ (2 * m) * (fourierCoeff m (m : ℤ) : ℂ) +
          (∑ i : Fin (2 * m),
            (fourierCoeff m ((i.val : ℤ) - (m : ℤ)) : ℂ) * z ^ i.val) =
        (∑ i : Fin (2 * m),
          (fourierCoeff m ((i.val : ℤ) - (m : ℤ)) : ℂ) * z ^ i.val) +
            (fourierCoeff m (m : ℤ) : ℂ) * z ^ (2 * m) := by ring
      _ = z ^ m * lam := hfull
      _ = lam * z ^ m := mul_comm _ _
  rw [LinearRecurrence.charPoly, Polynomial.IsRoot.def, Polynomial.eval]
  simp only [Polynomial.eval₂_finsetSum, one_mul, RingHom.id_apply,
    Polynomial.eval₂_monomial, Polynomial.eval₂_sub]
  change z ^ (2 * m) -
    (∑ i : Fin (2 * m), (fourierRecurrence m lam).coeffs i * z ^ i.val) = 0
  rw [hrecSum, ← hbase, sub_self]

#print axioms fourierCoeff_shifted_laurent_sum
#print axioms fourierRecurrence_charPoly_isRoot

end MF21Restart
