import Mathlib.Algebra.LinearRecurrence
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
Distinct characteristic roots form a basis of recurrence solutions, as
used in the paragraph following equation (13) of the frozen manuscript.
The actual Fourier recurrence and ghost constraints are separate bridges.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix

namespace MF21Restart

lemma geometric_sum_isSolution (E : LinearRecurrence ℂ)
    (w c : Fin E.order → ℂ) (hw : ∀ i, E.charPoly.IsRoot (w i)) :
    E.IsSolution (fun k => ∑ i, c i * w i ^ k) := by
  have hgeom : ∀ i, E.IsSolution (fun k => w i ^ k) :=
    fun i => (E.geom_sol_iff_root_charPoly (w i)).mpr (hw i)
  intro n
  calc
    ∑ i, c i * w i ^ (n + E.order) =
        ∑ i, c i * ∑ j, E.coeffs j * w i ^ (n + j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun z => c i * z) (hgeom i n)
    _ = ∑ j, E.coeffs j * ∑ i, c i * w i ^ (n + j) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Vandermonde nonsingularity supplies the coefficients; recurrence
uniqueness extends the initial agreement to every index. -/
theorem recurrence_solution_geometric_basis (E : LinearRecurrence ℂ)
    (w : Fin E.order → ℂ) (hinj : Function.Injective w)
    (hw : ∀ i, E.charPoly.IsRoot (w i))
    (u : ℕ → ℂ) (hu : E.IsSolution u) :
    ∃! c : Fin E.order → ℂ, ∀ k : ℕ, u k = ∑ i, c i * w i ^ k := by
  classical
  let V := (Matrix.vandermonde w).transpose
  have hdet : V.det ≠ 0 := by
    simpa only [V, Matrix.det_transpose] using
      (Matrix.det_vandermonde_ne_zero_iff.mpr hinj)
  let init : Fin E.order → ℂ := fun i => u i.val
  let c := V⁻¹ *ᵥ init
  have hc : V *ᵥ c = init := by
    dsimp only [c]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  have hinit : ∀ i : Fin E.order, (∑ j, c j * w j ^ i.val) = u i.val := by
    intro i
    have hi := congrFun hc i
    simpa only [V, init, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Matrix.vandermonde_apply, mul_comm] using hi
  have hsum := geometric_sum_isSolution E w c hw
  have heq : u = (fun k => ∑ i, c i * w i ^ k) := by
    apply (E.eq_iff_eqOn_range_order _ _ hu hsum).mpr
    intro k hk
    exact (hinit ⟨k, Finset.mem_range.mp hk⟩).symm
  refine ⟨c, fun k => congrFun heq k, ?_⟩
  intro c' hc'
  apply Matrix.mulVec_injective_of_det_ne_zero hdet
  funext i
  change (∑ j, w j ^ i.val * c' j) = ∑ j, w j ^ i.val * c j
  simpa only [mul_comm] using (hc' i.val).symm.trans (congrFun heq i.val)

/-- A nonzero geometric combination cannot vanish on a full block of
consecutive indices. The nonzero-root hypothesis is needed for shifts. -/
theorem geometric_coefficients_zero_of_consecutive_zeros {d : ℕ}
    (w c : Fin d → ℂ) (hinj : Function.Injective w)
    (hnonzero : ∀ i, w i ≠ 0) (a : ℕ)
    (hzero : ∀ k : Fin d, ∑ i, c i * w i ^ (a + k.val) = 0) : c = 0 := by
  let V := (Matrix.vandermonde w).transpose
  have hdet : V.det ≠ 0 := by
    simpa only [V, Matrix.det_transpose] using
      (Matrix.det_vandermonde_ne_zero_iff.mpr hinj)
  have hmul : V *ᵥ (fun i => c i * w i ^ a) = 0 := by
    funext k
    have hk := hzero k
    simp only [pow_add] at hk
    change (∑ i, w i ^ k.val * (c i * w i ^ a)) = 0
    convert hk using 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hz := Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  funext i
  have hi := congrFun hz i
  exact (mul_eq_zero.mp hi).resolve_right (pow_ne_zero _ (hnonzero i))

#print axioms recurrence_solution_geometric_basis
#print axioms geometric_coefficients_zero_of_consecutive_zeros

end MF21Restart
