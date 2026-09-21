import MF21Restart.BoundaryRecurrence
import MF21Restart.ToeplitzRecurrence
import MF21Restart.FourierRecurrenceEquation

/-! The boundary determinant has a zero exactly at a finite Toeplitz
eigenvalue, provided the supplied list is the distinct characteristic root
list. Construction of the manuscript's smooth list remains separate. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix

namespace MF21Restart

theorem boundaryDeterminant_zero_iff_toeplitz_eigenvector
    (m n : ℕ) (hm : 1 ≤ m) (lam : ℂ) (w : Fin (2 * m) → ℂ)
    (hinj : Function.Injective w) (hnonzero : ∀ i, w i ≠ 0)
    (hvalue : ∀ i, (2 - w i - (w i)⁻¹) ^ m = lam) :
    (boundaryMatrix m n w).det = 0 ↔
      ∃ v : Fin n → ℂ, v ≠ 0 ∧
        (toeplitz m n).map Complex.ofReal *ᵥ v = lam • v := by
  let a := (fourierRecurrence m lam).coeffs
  have hroot : ∀ i, (LinearRecurrence.mk (2 * m) a).charPoly.IsRoot (w i) :=
    fun i => fourierRecurrence_charPoly_isRoot m hm lam (w i) (hnonzero i) (hvalue i)
  have hb := boundaryDeterminant_zero_iff_recurrence_ghosts
    m n a w hinj hnonzero hroot
  have hf := finite_recurrence_iff_ghost_solution m n a
  refine hb.trans (hf.symm.trans ?_)
  constructor
  · rintro ⟨v, hv, hrec⟩
    refine ⟨v, hv, ?_⟩
    funext k
    have hk := (fourierRecurrence_equation_iff m hm lam
      (zeroGhostExtension m n v) k.val).mp (hrec k)
    rw [zeroGhost_convolution_eq_toeplitz_mulVec] at hk
    have hmid : zeroGhostExtension m n v (k.val + m) = v k := by
      simpa only [Nat.add_comm] using zeroGhostExtension_middle m n v k
    simpa only [hmid, Pi.smul_apply, smul_eq_mul] using hk
  · rintro ⟨v, hv, hvec⟩
    refine ⟨v, hv, ?_⟩
    intro k
    apply (fourierRecurrence_equation_iff m hm lam
      (zeroGhostExtension m n v) k.val).mpr
    rw [zeroGhost_convolution_eq_toeplitz_mulVec]
    have hmid : zeroGhostExtension m n v (k.val + m) = v k := by
      simpa only [Nat.add_comm] using zeroGhostExtension_middle m n v k
    simpa only [hmid, Pi.smul_apply, smul_eq_mul] using congrFun hvec k

#print axioms boundaryDeterminant_zero_iff_toeplitz_eigenvector

end MF21Restart
