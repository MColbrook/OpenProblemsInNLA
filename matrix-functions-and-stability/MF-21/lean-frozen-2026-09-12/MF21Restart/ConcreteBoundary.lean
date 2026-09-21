import MF21Restart.CharacteristicRoots
import MF21Restart.RealComplexEigenvalue
import MF21Restart.BoundaryMultiplicity

set_option autoImplicit false
noncomputable section

namespace MF21Restart

def manuscriptBoundaryDeterminant (m n : ℕ) (θ : ℝ) : ℂ :=
  (boundaryMatrix m n (characteristicRoots m θ)).det

theorem eigenvalue_iff_manuscriptBoundaryDeterminant_zero
    (m n : ℕ) (hm : 2 ≤ m) (θ : ℝ) (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    (∃ j : ℕ, 1 ≤ j ∧ j ≤ n ∧ eigenvalue m n j = symbol m θ) ↔
      manuscriptBoundaryDeterminant m n θ = 0 :=
  eigenvalue_index_iff_boundaryDeterminant_zero m n (by omega)
    (symbol m θ) (characteristicRoots m θ)
    (characteristicRoots_injective m hm θ hθ hθπ)
    (characteristicRoots_ne_zero m θ) (characteristicRoots_equation m hm θ)

theorem manuscript_boundary_kernel_finrank_eq_eigenspace
    (m n : ℕ) (hm : 2 ≤ m) (θ : ℝ) (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    Module.finrank ℂ (LinearMap.ker (boundaryMatrix m n (characteristicRoots m θ)).mulVecLin) =
      Module.finrank ℂ
        (Module.End.eigenspace ((toeplitz m n).map Complex.ofReal).mulVecLin (symbol m θ : ℂ)) :=
  boundary_kernel_finrank_eq_eigenspace m n (by omega)
    (symbol m θ : ℂ) (characteristicRoots m θ)
    (characteristicRoots_injective m hm θ hθ hθπ)
    (characteristicRoots_ne_zero m θ) (characteristicRoots_equation m hm θ)

theorem characteristicRoots_contDiff (m : ℕ) (hm : 2 ≤ m) (i : Fin (2 * m)) :
    ContDiff ℝ ⊤ (fun θ : ℝ => characteristicRoots m θ i) := by
  have hi := i.isLt
  have hz : ContDiff ℝ ⊤ oscillatoryRoot :=
    ((Complex.contDiff_exp : ContDiff ℂ ⊤ Complex.exp).restrict_scalars ℝ).comp
      (Complex.ofRealCLM.contDiff.mul contDiff_const)
  unfold characteristicRoots
  split_ifs with hleft hunit hinverse
  · exact stableRootCurve_contDiff _ (rootKappa_re_pos m (i.val + 1) (by omega) (by omega))
  · exact hz
  · exact hz.inv oscillatoryRoot_ne_zero
  · exact (stableRootCurve_contDiff _
      (rootKappa_re_pos m (i.val - m) (by omega) (by omega))).inv
        (stableRootCurve_ne_zero _)

theorem manuscriptBoundaryDeterminant_pi (m n : ℕ) (hm : 2 ≤ m) :
    manuscriptBoundaryDeterminant m n Real.pi = 0 := by
  let a : Fin (2 * m) := ⟨m - 1, by omega⟩
  let b : Fin (2 * m) := ⟨m, by omega⟩
  have hab : a ≠ b := by
    intro h
    have hval := congrArg Fin.val h
    dsimp [a, b] at hval
    omega
  have hw : characteristicRoots m Real.pi a = characteristicRoots m Real.pi b := by
    rw [characteristicRoots_unit m Real.pi a rfl,
      characteristicRoots_unit_inv m hm Real.pi b rfl]
    simp only [oscillatoryRoot, Complex.exp_pi_mul_I, inv_neg, inv_one]
  apply Matrix.det_zero_of_column_eq hab
  intro k
  simp only [boundaryMatrix, Matrix.of_apply, hw]

#print axioms eigenvalue_iff_manuscriptBoundaryDeterminant_zero
#print axioms manuscript_boundary_kernel_finrank_eq_eigenspace
#print axioms characteristicRoots_contDiff
#print axioms manuscriptBoundaryDeterminant_pi

end MF21Restart
