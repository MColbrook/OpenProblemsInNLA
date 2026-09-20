import Mathlib.Algebra.LinearRecurrence
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Distinct characteristic roots span the full recurrence solution space.
This supplies the finite-dimensional basis step in the boundary determinant. -/
noncomputable section
open scoped BigOperators
open Finset Matrix
namespace MF21Recurrence

theorem geometric_combination_solution (E : LinearRecurrence ℂ)
    (roots c : Fin E.order → ℂ)
    (hr : ∀ j, E.charPoly.IsRoot (roots j)) :
    E.IsSolution (fun n => ∑ j, c j * (roots j)^n) := by
  have hmem : (∑ j, c j • (fun n : ℕ => (roots j)^n)) ∈ E.solSpace := by
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    exact (E.geom_sol_iff_root_charPoly (roots j)).mpr (hr j)
  change E.IsSolution (∑ j, c j • (fun n : ℕ => (roots j)^n)) at hmem
  have he : (∑ j, c j • (fun n : ℕ => (roots j)^n)) =
      (fun n => ∑ j, c j * (roots j)^n) := by
    funext n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rwa [he] at hmem

/-- Every solution is a linear combination of the geometric solutions when
the characteristic polynomial has the full number of distinct roots. -/
theorem solution_eq_geometric_combination (E : LinearRecurrence ℂ)
    (roots : Fin E.order → ℂ) (hinj : Function.Injective roots)
    (hr : ∀ j, E.charPoly.IsRoot (roots j))
    (u : ℕ → ℂ) (hu : E.IsSolution u) :
    ∃ c : Fin E.order → ℂ, ∀ n, u n = ∑ j, c j * (roots j)^n := by
  let V : Matrix (Fin E.order) (Fin E.order) ℂ := (Matrix.vandermonde roots)ᵀ
  have hdet : IsUnit V.det := by
    apply isUnit_iff_ne_zero.mpr
    simpa [V, Matrix.det_transpose] using (Matrix.det_vandermonde_ne_zero_iff.mpr hinj)
  obtain ⟨c, hc⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det V).mpr hdet) (fun i : Fin E.order => u i)
  refine ⟨c, ?_⟩
  have hv := geometric_combination_solution E roots c hr
  have he : u = fun n => ∑ j, c j * (roots j)^n := by
    apply (E.eq_iff_eqOn_range_order u _ hu hv).mpr
    intro n hn
    have hn' := Finset.mem_range.mp hn
    have h := congrFun hc (⟨n, hn'⟩ : Fin E.order)
    simpa [V, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Matrix.vandermonde_apply, mul_comm] using h.symm
  exact fun n => congrFun he n

/-- The geometric coefficients are unique. -/
theorem geometric_coefficients_unique {d : ℕ} (roots c b : Fin d → ℂ)
    (hinj : Function.Injective roots)
    (heq : ∀ n : Fin d, (∑ j, c j * (roots j)^n.val) = ∑ j, b j * (roots j)^n.val) :
    c = b := by
  have hz : c-b = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hinj
    intro n
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, heq, sub_self]
  exact sub_eq_zero.mp hz

end MF21Recurrence
#print axioms MF21Recurrence.solution_eq_geometric_combination
#print axioms MF21Recurrence.geometric_coefficients_unique
