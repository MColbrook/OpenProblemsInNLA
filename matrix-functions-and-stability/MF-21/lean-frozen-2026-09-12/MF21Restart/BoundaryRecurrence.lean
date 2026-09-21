import MF21Restart.BoundaryExpansion
import MF21Restart.RecurrenceBasis
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! The exact ghost determinant as a criterion for recurrence solutions.
Its specialization to the Fourier recurrence remains a separate bridge. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix

namespace MF21Restart

lemma boundary_mulVec_upper (m n : ℕ) (w c : Fin (2 * m) → ℂ) (k : Fin m) :
    (boundaryMatrix m n w *ᵥ c) (boundaryRowEquiv m (Sum.inl k)) =
      ∑ i, c i * w i ^ k.val := by
  simp [Matrix.mulVec, dotProduct, boundaryMatrix, boundaryRowEquiv_inl_val,
    k.isLt, mul_comm]

lemma boundary_mulVec_lower (m n : ℕ) (w c : Fin (2 * m) → ℂ) (k : Fin m) :
    (boundaryMatrix m n w *ᵥ c) (boundaryRowEquiv m (Sum.inr k)) =
      ∑ i, c i * w i ^ (n + m + k.val) := by
  simp [Matrix.mulVec, dotProduct, boundaryMatrix, boundaryRowEquiv_inr_val,
    Nat.add_assoc, mul_comm]

theorem boundary_mulVec_zero_iff_ghosts
    (m n : ℕ) (w c : Fin (2 * m) → ℂ) :
    boundaryMatrix m n w *ᵥ c = 0 ↔
      (∀ k : Fin m, ∑ i, c i * w i ^ k.val = 0) ∧
      (∀ k : Fin m, ∑ i, c i * w i ^ (n + m + k.val) = 0) := by
  constructor
  · intro h
    constructor
    · intro k
      have hk := congrFun h (boundaryRowEquiv m (Sum.inl k))
      simpa only [boundary_mulVec_upper, Pi.zero_apply] using hk
    · intro k
      have hk := congrFun h (boundaryRowEquiv m (Sum.inr k))
      simpa only [boundary_mulVec_lower, Pi.zero_apply] using hk
  · rintro ⟨hupper, hlower⟩
    funext row
    obtain ⟨k, rfl⟩ := (boundaryRowEquiv m).surjective row
    cases k with
    | inl k => simpa only [boundary_mulVec_upper, Pi.zero_apply] using hupper k
    | inr k => simpa only [boundary_mulVec_lower, Pi.zero_apply] using hlower k

/-- The determinant criterion is proved from the root basis and the two
actual ghost ranges. It is not an assumed property of an abstract determinant. -/
theorem boundaryDeterminant_zero_iff_recurrence_ghosts
    (m n : ℕ) (a w : Fin (2 * m) → ℂ)
    (hinj : Function.Injective w) (hnonzero : ∀ i, w i ≠ 0)
    (hroot : ∀ i, (LinearRecurrence.mk (2 * m) a).charPoly.IsRoot (w i)) :
    (boundaryMatrix m n w).det = 0 ↔
      ∃ u : ℕ → ℂ, (LinearRecurrence.mk (2 * m) a).IsSolution u ∧ u ≠ 0 ∧
        (∀ k : Fin m, u k.val = 0) ∧
        (∀ k : Fin m, u (n + m + k.val) = 0) := by
  classical
  constructor
  · intro hdet
    obtain ⟨c, hcne, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hghost := (boundary_mulVec_zero_iff_ghosts m n w c).mp hc
    let u : ℕ → ℂ := fun k => ∑ i, c i * w i ^ k
    refine ⟨u, geometric_sum_isSolution (LinearRecurrence.mk (2 * m) a) w c hroot,
      ?_, hghost.1, hghost.2⟩
    intro hz
    apply hcne
    apply geometric_coefficients_zero_of_consecutive_zeros w c hinj hnonzero 0
    intro k
    have hk := congrFun hz k.val
    simpa only [u, zero_add, Pi.zero_apply] using hk
  · rintro ⟨u, hu, hune, hupper, hlower⟩
    obtain ⟨c, hc, _⟩ := recurrence_solution_geometric_basis
      (LinearRecurrence.mk (2 * m) a) w hinj hroot u hu
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨c, ?_, (boundary_mulVec_zero_iff_ghosts m n w c).mpr ?_⟩
    · intro hz
      apply hune
      funext k
      simpa [hz] using hc k
    · constructor
      · intro k
        rw [← hc k.val]
        exact hupper k
      · intro k
        rw [← hc (n + m + k.val)]
        exact hlower k

#print axioms boundary_mulVec_zero_iff_ghosts
#print axioms boundaryDeterminant_zero_iff_recurrence_ghosts

end MF21Restart
