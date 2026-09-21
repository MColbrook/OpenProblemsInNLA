import MF21Restart.RootDistinctness
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
Conjugacy and pairwise distinctness of the actual stable root curves.
Conjugation of the principal square root is used only on the proved slit
plane; distinctness follows from the exact reciprocal root equations.
STABLE_ROOT_SYMMETRY_STATEMENTS.md locks the scope before these proofs.
-/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

private lemma sqrt_conj_of_mem_slitPlane (z : ℂ) (hz : z ∈ Complex.slitPlane) :
    (starRingEnd ℂ) (Complex.sqrt z) = Complex.sqrt ((starRingEnd ℂ) z) := by
  simpa only [Complex.sqrt, map_inv₀, map_ofNat] using
    (Complex.conj_cpow z (2⁻¹ : ℂ) (Complex.slitPlane_arg_ne_pi hz)).symm

theorem stableRootCurve_conj (κ : ℂ) (hκ : 0 < κ.re) (theta : ℝ) :
    (starRingEnd ℂ) (stableRootCurve κ theta) =
      stableRootCurve ((starRingEnd ℂ) κ) theta := by
  unfold stableRootCurve stableQuadraticRoot
  rw [map_pow, map_sub,
    sqrt_conj_of_mem_slitPlane _ (stableRootCurve_sqrt_argument_mem_slitPlane κ hκ theta)]
  simp only [map_add, map_one, map_pow, map_mul, Complex.conj_ofReal]

theorem stableRootCurve_rootKappa_conj (m ell : ℕ)
    (hell : 1 ≤ ell) (hellm : ell < m) (theta : ℝ) :
    (starRingEnd ℂ) (stableRootCurve (rootKappa m ell) theta) =
      stableRootCurve (rootKappa m (m - ell)) theta := by
  calc
    (starRingEnd ℂ) (stableRootCurve (rootKappa m ell) theta) =
        stableRootCurve ((starRingEnd ℂ) (rootKappa m ell)) theta :=
      stableRootCurve_conj _ (rootKappa_re_pos m ell hell hellm) theta
    _ = stableRootCurve (rootKappa m (m - ell)) theta := by
      rw [rootKappa_conj m ell hell hellm]

theorem stableRootCurve_rootKappa_injective
    (m : ℕ) (theta : ℝ) (htheta : 0 < theta) (htheta_pi : theta ≤ Real.pi) :
    Function.Injective (fun ell : {ell : ℕ // 1 ≤ ell ∧ ell < m} =>
      stableRootCurve (rootKappa m ell.val) theta) := by
  intro a b hab
  change stableRootCurve (rootKappa m a.val) theta =
    stableRootCurve (rootKappa m b.val) theta at hab
  have hs : 0 < Real.sin (theta / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hcos := Real.cos_two_mul_eq_one_sub (theta / 2)
  rw [show 2 * (theta / 2) = theta by ring] at hcos
  have hgpos : 0 < 2 - 2 * Real.cos theta := by
    nlinarith [sq_pos_of_pos hs]
  have hg : ((2 - 2 * Real.cos theta : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hgpos)
  have homega_mul :
      rootOmega m a.val * ((2 - 2 * Real.cos theta : ℝ) : ℂ) =
        rootOmega m b.val * ((2 - 2 * Real.cos theta : ℝ) : ℂ) := by
    calc
      rootOmega m a.val * ((2 - 2 * Real.cos theta : ℝ) : ℂ) =
          2 - stableRootCurve (rootKappa m a.val) theta -
            (stableRootCurve (rootKappa m a.val) theta)⁻¹ :=
        (stableRootCurve_rootOmega_equation m a.val theta).symm
      _ = 2 - stableRootCurve (rootKappa m b.val) theta -
          (stableRootCurve (rootKappa m b.val) theta)⁻¹ := by rw [hab]
      _ = rootOmega m b.val * ((2 - 2 * Real.cos theta : ℝ) : ℂ) :=
        stableRootCurve_rootOmega_equation m b.val theta
  have homega : rootOmega m a.val = rootOmega m b.val :=
    mul_right_cancel₀ hg homega_mul
  have hfin : (⟨a.val, a.property.2⟩ : Fin m) = ⟨b.val, b.property.2⟩ :=
    rootOmega_injective m homega
  apply Subtype.ext
  exact congrArg Fin.val hfin

#print axioms stableRootCurve_conj
#print axioms stableRootCurve_rootKappa_conj
#print axioms stableRootCurve_rootKappa_injective

end MF21Restart
