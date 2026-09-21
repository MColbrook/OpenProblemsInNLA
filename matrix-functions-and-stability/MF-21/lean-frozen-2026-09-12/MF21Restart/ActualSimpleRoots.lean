import MF21Restart.DeterminantRemainder
import MF21Restart.SimpleDeterminant
import MF21Restart.EigenvalueMultiplicity
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Matrix.Normed

/-!
The concrete simple-root bridge from manuscript Lemma 4. A simple zero
of the actual scalar residual gives a one-dimensional actual Toeplitz
eigenspace and a unique original one-based eigenvalue index. No phase-cell
existence, ordering, or identification of that index is asserted here.
The statement lock is `ACTUAL_SIMPLE_ROOTS_STATEMENTS.md`.
-/

set_option autoImplicit false
noncomputable section
open scoped Topology Matrix.Norms.Elementwise
open Filter Matrix

namespace MF21Restart

def manuscriptResidual (m n : ℕ) (hm : 2 ≤ m) (θ : ℝ) : ℝ :=
  Real.sin (manuscriptPhaseFn m n θ) + manuscriptError m n hm θ

theorem manuscriptResidual_hasDerivAt (m n : ℕ) (hm : 2 ≤ m)
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi) :
    HasDerivAt (manuscriptResidual m n hm)
      (Real.cos (manuscriptPhaseFn m n θ) * deriv (manuscriptPhaseFn m n) θ +
        deriv (manuscriptError m n hm) θ) θ := by
  have hF := (manuscriptPhaseFn_hasDerivAt m n (by omega) θ hθ).differentiableAt
  have hE := (manuscriptError_contDiffAt m n hm θ hθ).differentiableAt (by simp)
  exact hF.hasDerivAt.sin.add hE.hasDerivAt

set_option backward.isDefEq.respectTransparency.types false in
/-- Smoothness is assembled from the concrete powers in every entry. -/
theorem manuscriptBoundaryMatrix_contDiff (m n : ℕ) (hm : 2 ≤ m) :
    ContDiff ℝ ⊤ (fun θ : ℝ => boundaryMatrix m n (characteristicRoots m θ)) := by
  apply contDiff_pi.mpr
  intro row
  apply contDiff_pi.mpr
  intro col
  by_cases hrow : row.val < m
  · simpa only [boundaryMatrix, Matrix.of_apply, if_pos hrow] using
      (characteristicRoots_contDiff m hm col).pow row.val
  · simpa only [boundaryMatrix, Matrix.of_apply, if_neg hrow] using
      (characteristicRoots_contDiff m hm col).pow (n + row.val)

theorem manuscriptBoundaryDeterminant_eq_normalizer_mul_residual
    (m n : ℕ) (hm : 2 ≤ m) (θ : ℝ) (hθ : 0 < θ) (hθπ : θ ≤ Real.pi) :
    manuscriptBoundaryDeterminant m n θ =
      manuscriptNormalizer m n θ * (manuscriptResidual m n hm θ : ℂ) := by
  have h := manuscriptNormalizedDeterminant_eq_sin_add_error m n hm θ hθ hθπ
  rw [← boundaryErrorExpression_real m n hm θ hθ hθπ, ← Complex.ofReal_add] at h
  change manuscriptBoundaryDeterminant m n θ / manuscriptNormalizer m n θ =
    (manuscriptResidual m n hm θ : ℂ) at h
  exact ((div_eq_iff (manuscriptNormalizer_ne_zero m n hm θ hθ hθπ)).mp h).trans
    (mul_comm _ _)

/-- The local identity is differentiated on an open neighborhood of the
interior zero. In particular, this does not differentiate a merely pointwise
equality at the zero. -/
theorem manuscriptBoundaryDeterminant_hasDerivAt_of_residual_zero
    (m n : ℕ) (hm : 2 ≤ m) (θ : ℝ) (hθ : 0 < θ) (hθπ : θ < Real.pi)
    (hzero : manuscriptResidual m n hm θ = 0) :
    HasDerivAt (manuscriptBoundaryDeterminant m n)
      (manuscriptNormalizer m n θ * ((deriv (manuscriptResidual m n hm) θ : ℝ) : ℂ)) θ := by
  have hN := ((manuscriptNormalizer_contDiff m n hm).differentiable (by simp) θ).hasDerivAt
  have hH := (manuscriptResidual_hasDerivAt m n hm θ
    ⟨hθ.le, hθπ.le⟩).differentiableAt.hasDerivAt
  have hprod := hN.mul hH.ofReal_comp
  simp only [hzero, Complex.ofReal_zero, mul_zero, zero_add] at hprod
  have hnb : Set.Ioo (0 : ℝ) Real.pi ∈ 𝓝 θ := isOpen_Ioo.mem_nhds ⟨hθ, hθπ⟩
  have heq : manuscriptBoundaryDeterminant m n =ᶠ[𝓝 θ]
      (fun t : ℝ => manuscriptNormalizer m n t * (manuscriptResidual m n hm t : ℂ)) := by
    filter_upwards [hnb] with t ht
    exact manuscriptBoundaryDeterminant_eq_normalizer_mul_residual m n hm t ht.1 ht.2.le
  exact hprod.congr_of_eventuallyEq heq

theorem manuscriptResidual_simple_zero_eigenspace_finrank
    (m n : ℕ) (hm : 2 ≤ m) (θ : ℝ) (hθ : 0 < θ) (hθπ : θ < Real.pi)
    (hzero : manuscriptResidual m n hm θ = 0)
    (hsimple : deriv (manuscriptResidual m n hm) θ ≠ 0) :
    Module.finrank ℂ
      (Module.End.eigenspace
        ((toeplitz m n).map Complex.ofReal).mulVecLin (symbol m θ : ℂ)) = 1 := by
  have hB := ((manuscriptBoundaryMatrix_contDiff m n hm).differentiable
    (by simp) θ).hasDerivAt
  have hD := manuscriptBoundaryDeterminant_hasDerivAt_of_residual_zero
    m n hm θ hθ hθπ hzero
  have hd : manuscriptNormalizer m n θ *
      ((deriv (manuscriptResidual m n hm) θ : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero (manuscriptNormalizer_ne_zero m n hm θ hθ hθπ.le)
      (Complex.ofReal_ne_zero.mpr hsimple)
  have hDzero : manuscriptBoundaryDeterminant m n θ = 0 := by
    rw [manuscriptBoundaryDeterminant_eq_normalizer_mul_residual m n hm θ hθ hθπ.le,
      hzero, Complex.ofReal_zero, mul_zero]
  exact toeplitz_eigenspace_finrank_eq_one_of_simple_boundary_zero
    m n (by omega) (symbol m θ : ℂ) (characteristicRoots m) θ
    (characteristicRoots_injective m hm θ hθ hθπ)
    (characteristicRoots_ne_zero m θ) (characteristicRoots_equation m hm θ)
    _ _ hB hD hd hDzero

/-- The unique index is in the original accessor's one-based range. This
does not yet identify it with a phase-cell label. -/
theorem manuscriptResidual_simple_zero_existsUnique_eigenvalue_index
    (m n : ℕ) (hm : 2 ≤ m) (θ : ℝ) (hθ : 0 < θ) (hθπ : θ < Real.pi)
    (hzero : manuscriptResidual m n hm θ = 0)
    (hsimple : deriv (manuscriptResidual m n hm) θ ≠ 0) :
    ∃! j : ℕ, 1 ≤ j ∧ j ≤ n ∧ eigenvalue m n j = symbol m θ :=
  existsUnique_eigenvalue_index_of_complex_eigenspace_finrank_one m n (symbol m θ)
    (manuscriptResidual_simple_zero_eigenspace_finrank m n hm θ hθ hθπ hzero hsimple)

#print axioms manuscriptResidual_hasDerivAt
#print axioms manuscriptBoundaryMatrix_contDiff
#print axioms manuscriptBoundaryDeterminant_eq_normalizer_mul_residual
#print axioms manuscriptBoundaryDeterminant_hasDerivAt_of_residual_zero
#print axioms manuscriptResidual_simple_zero_eigenspace_finrank
#print axioms manuscriptResidual_simple_zero_existsUnique_eigenvalue_index

end MF21Restart
