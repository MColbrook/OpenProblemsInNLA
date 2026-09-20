import MF21.BoundaryDeterminant
import MF21.LaurentSymbol

/-! Exact bridge between the recurrence characteristic polynomial and the
Laurent symbol. -/
noncomputable section
open scoped BigOperators
open Finset
namespace MF21Boundary

theorem charPoly_root_iff_laurent (m : ℕ) (hm : 0 < m)
    (lam z : ℂ) (hz : z ≠ 0) :
    (recurrence m lam).charPoly.IsRoot z ↔ (2-z-z⁻¹)^m = lam := by
  rw [← (recurrence m lam).geom_sol_iff_root_charPoly]
  constructor
  · intro h
    have he := (recurrence_at_iff m hm lam (fun n => z^n) 0).mp (h 0)
    simp only [zero_add] at he
    change (∑ l ∈ range (2*m+1), (MF21FirstColumn.central m l : ℂ)*z^l) = lam*z^m at he
    rw [MF21Laurent.central_sum_eq_laurent m z hz] at he
    apply mul_left_cancel₀ (pow_ne_zero m hz)
    simpa only [mul_comm] using he
  · intro h n
    exact (recurrence_at_iff m hm lam (fun k => z^k) n).mpr
      (MF21Laurent.geometric_stencil m n z lam hz h)

end MF21Boundary
#print axioms MF21Boundary.charPoly_root_iff_laurent
