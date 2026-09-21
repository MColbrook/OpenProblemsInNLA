import MF21Restart.DeterminantMultiplicity
import MF21Restart.BoundaryMultiplicity

set_option autoImplicit false
noncomputable section

namespace MF21Restart

theorem finrank_ker_eq_one_of_simple_determinant_zero
    (N : ℕ) (M : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (M' : Matrix (Fin N) (Fin N) ℂ) (θ : ℝ) (d : ℂ)
    (hM : HasDerivAt M M' θ)
    (hD : HasDerivAt (fun t : ℝ => (M t).det) d θ)
    (hd : d ≠ 0) (hzero : (M θ).det = 0) :
    Module.finrank ℂ (LinearMap.ker (M θ).mulVecLin) = 1 := by
  have hpos : 0 < Module.finrank ℂ (LinearMap.ker (M θ).mulVecLin) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    obtain ⟨v, hvne, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hzero
    have hmem : v ∈ LinearMap.ker (M θ).mulVecLin := hv
    refine ⟨⟨v, hmem⟩, ?_⟩
    intro hz
    exact hvne (congrArg Subtype.val hz)
  have hlt : Module.finrank ℂ (LinearMap.ker (M θ).mulVecLin) < 2 := by
    by_contra hn
    have h0 := hasDerivAt_det_zero_of_two_le_finrank_ker
      N M M' θ hM (le_of_not_gt hn)
    exact hd (hD.unique h0)
  omega

theorem toeplitz_eigenspace_finrank_eq_one_of_simple_boundary_zero
    (m n : ℕ) (hm : 1 ≤ m) (lam : ℂ)
    (w : ℝ → Fin (2 * m) → ℂ) (θ : ℝ)
    (hinj : Function.Injective (w θ)) (hnonzero : ∀ i, w θ i ≠ 0)
    (hvalue : ∀ i, (2 - w θ i - (w θ i)⁻¹) ^ m = lam)
    (B' : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ) (d : ℂ)
    (hB : HasDerivAt (fun t : ℝ => boundaryMatrix m n (w t)) B' θ)
    (hD : HasDerivAt (fun t : ℝ => (boundaryMatrix m n (w t)).det) d θ)
    (hd : d ≠ 0) (hzero : (boundaryMatrix m n (w θ)).det = 0) :
    Module.finrank ℂ
      (Module.End.eigenspace ((toeplitz m n).map Complex.ofReal).mulVecLin lam) = 1 := by
  rw [← boundary_kernel_finrank_eq_eigenspace m n hm lam (w θ) hinj hnonzero hvalue]
  exact finrank_ker_eq_one_of_simple_determinant_zero
    (2 * m) (fun t => boundaryMatrix m n (w t)) B' θ d hB hD hd hzero

#print axioms finrank_ker_eq_one_of_simple_determinant_zero
#print axioms toeplitz_eigenspace_finrank_eq_one_of_simple_boundary_zero

end MF21Restart
