import MF21Restart.FourierStencil
import Mathlib.Algebra.BigOperators.Finprod

/-!
The exact finite Laurent polynomial of the concrete MF-21 Fourier coefficients.
All finite-support sum manipulations below have proved finite support; no
convergence or spectral asymptotic hypothesis is introduced.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

private lemma fourierCoeff_complex_support_subset (m : ℕ) :
    Function.support (fun k : ℤ => (fourierCoeff m k : ℂ)) ⊆
      (Finset.Icc (-(m : ℤ)) (m : ℤ) : Set ℤ) := by
  intro k hk
  by_contra hmem
  have hlarge : (m : ℤ) < |k| := by
    by_contra h
    exact hmem (Finset.mem_Icc.mpr (abs_le.mp (le_of_not_gt h)))
  exact hk (by simp [fourierCoeff_support m k hlarge])

private lemma fourierCoeff_complex_hasFiniteSupport (m : ℕ) :
    Function.HasFiniteSupport (fun k : ℤ => (fourierCoeff m k : ℂ)) :=
  (Finset.Icc (-(m : ℤ)) (m : ℤ)).finite_toSet.subset
    (fourierCoeff_complex_support_subset m)

private lemma fourierCoeff_laurent_shift (m : ℕ) (r : ℤ) (z : ℂ) (hz : z ≠ 0) :
    (∑ᶠ k : ℤ, (fourierCoeff m (k - r) : ℂ) * z ^ k) =
      (∑ᶠ k : ℤ, (fourierCoeff m k : ℂ) * z ^ k) * z ^ r := by
  rw [finsum_mul]
  apply finsum_eq_of_bijective (fun k : ℤ => k - r)
  · constructor
    · intro a b h
      change a - r = b - r at h
      omega
    · intro k
      refine ⟨k + r, ?_⟩
      change k + r - r = k
      omega
  · intro k
    rw [mul_assoc, ← zpow_add₀ hz, sub_add_cancel]

private theorem fourierCoeff_laurent_finsum (m : ℕ) (z : ℂ) (hz : z ≠ 0) :
    (∑ᶠ k : ℤ, (fourierCoeff m k : ℂ) * z ^ k) = (2 - z - z⁻¹) ^ m := by
  induction m with
  | zero =>
      rw [finsum_eq_single _ (0 : ℤ)]
      · simp [fourierCoeff_zero]
      · intro k hk
        simp [fourierCoeff_zero, hk]
  | succ m ih =>
      have hc := fourierCoeff_complex_hasFiniteSupport m
      have hcminus : Function.HasFiniteSupport
          (fun k : ℤ => (fourierCoeff m (k - 1) : ℂ)) :=
        Function.HasFiniteSupport.fun_comp_of_injective
          (f := fun k : ℤ => (fourierCoeff m k : ℂ))
          (g := fun k : ℤ => k - 1)
          (by intro a b h; change a - 1 = b - 1 at h; omega) hc
      have hcplus : Function.HasFiniteSupport
          (fun k : ℤ => (fourierCoeff m (k + 1) : ℂ)) :=
        Function.HasFiniteSupport.fun_comp_of_injective
          (f := fun k : ℤ => (fourierCoeff m k : ℂ))
          (g := fun k : ℤ => k + 1)
          (by intro a b h; change a + 1 = b + 1 at h; omega) hc
      have hw : Function.HasFiniteSupport
          (fun k : ℤ => (fourierCoeff m k : ℂ) * z ^ k) :=
        hc.mul_left (fun k => z ^ k)
      have htwo : Function.HasFiniteSupport
          (fun k : ℤ => 2 * ((fourierCoeff m k : ℂ) * z ^ k)) :=
        hw.fun_comp (g := fun w : ℂ => 2 * w) (by simp)
      have hminus : Function.HasFiniteSupport
          (fun k : ℤ => (fourierCoeff m (k - 1) : ℂ) * z ^ k) :=
        hcminus.mul_left (fun k => z ^ k)
      have hplus : Function.HasFiniteSupport
          (fun k : ℤ => (fourierCoeff m (k + 1) : ℂ) * z ^ k) :=
        hcplus.mul_left (fun k => z ^ k)
      have hrecur :
          (fun k : ℤ => (fourierCoeff (m + 1) k : ℂ) * z ^ k) =
          (fun k : ℤ => 2 * ((fourierCoeff m k : ℂ) * z ^ k) -
            (fourierCoeff m (k - 1) : ℂ) * z ^ k -
              (fourierCoeff m (k + 1) : ℂ) * z ^ k) := by
        funext k
        rw [fourierCoeff_succ]
        push_cast
        ring
      have hshiftminus :
          (∑ᶠ k : ℤ, (fourierCoeff m (k - 1) : ℂ) * z ^ k) =
            (∑ᶠ k : ℤ, (fourierCoeff m k : ℂ) * z ^ k) * z := by
        simpa using fourierCoeff_laurent_shift m 1 z hz
      have hshiftplus :
          (∑ᶠ k : ℤ, (fourierCoeff m (k + 1) : ℂ) * z ^ k) =
            (∑ᶠ k : ℤ, (fourierCoeff m k : ℂ) * z ^ k) * z⁻¹ := by
        simpa using fourierCoeff_laurent_shift m (-1) z hz
      have hsplit := finsum_sub_distrib (htwo.sub hminus) hplus
      simp only [Pi.sub_apply] at hsplit
      rw [hrecur, hsplit,
        finsum_sub_distrib htwo hminus, ← mul_finsum, hshiftminus, hshiftplus,
        ih, pow_succ]
      ring

/-- The finite Laurent polynomial of the actual Fourier coefficients is
the mth power of the second-difference symbol at every nonzero complex z. -/
theorem fourierCoeff_laurent_sum (m : ℕ) (z : ℂ) (hz : z ≠ 0) :
    (∑ k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
      (fourierCoeff m k : ℂ) * z ^ k) =
      (2 - z - z⁻¹) ^ m := by
  have hs : Function.support (fun k : ℤ => (fourierCoeff m k : ℂ) * z ^ k) ⊆
      (Finset.Icc (-(m : ℤ)) (m : ℤ) : Set ℤ) := by
    intro k hk
    apply fourierCoeff_complex_support_subset m
    intro hc
    exact hk (by simp [hc])
  rw [← finsum_eq_finsetSum_of_support_subset _ hs]
  exact fourierCoeff_laurent_finsum m z hz

#print axioms fourierCoeff_laurent_sum

end MF21Restart
