import MF21Restart.SpectralEnclosure
import MF21Restart.EigenvalueBridge
import MF21Restart.MatrixInverseAlgebra
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Fin

/-! The actual inverse trace equals the sum over every original sorted
eigenvalue. Prior lock: INVERSE_SPECTRAL_TRACE_STATEMENTS.md. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Unitary

namespace MF21Restart

theorem posDef_inverse_trace (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    Matrix.trace A⁻¹ = ∑ i : Fin n, (hA.isHermitian.eigenvalues i)⁻¹ := by
  classical
  let H := hA.isHermitian
  let e := conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ) H.eigenvectorUnitary
  have hspec : A = e (Matrix.diagonal H.eigenvalues) := by
    simpa only [e, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using H.spectral_theorem
  have hD : Matrix.diagonal H.eigenvalues *
      Matrix.diagonal (fun i => (H.eigenvalues i)⁻¹) = 1 :=
    diagonal_mul_reciprocal H.eigenvalues (fun i => ne_of_gt (hA.eigenvalues_pos i))
  have hright : A * e (Matrix.diagonal (fun i => (H.eigenvalues i)⁻¹)) = 1 := by
    calc
      A * e (Matrix.diagonal (fun i => (H.eigenvalues i)⁻¹)) =
          e (Matrix.diagonal H.eigenvalues) *
            e (Matrix.diagonal (fun i => (H.eigenvalues i)⁻¹)) :=
        congrArg (fun M : Matrix (Fin n) (Fin n) ℝ =>
          M * e (Matrix.diagonal (fun i => (H.eigenvalues i)⁻¹))) hspec
      _ = 1 := by rw [← map_mul, hD, map_one]
  rw [Matrix.inv_eq_right_inv hright]
  change Matrix.trace (conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ) H.eigenvectorUnitary
    (Matrix.diagonal (fun i => (H.eigenvalues i)⁻¹))) = _
  rw [conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  have hU : (star H.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) * H.eigenvectorUnitary = 1 :=
    H.eigenvectorUnitary.2.1
  rw [hU, one_mul, Matrix.trace_diagonal]

theorem sum_orderedEigenvalue_map (m n : ℕ) (f : ℝ → ℝ) :
    (∑ i : Fin n, f (orderedEigenvalue m n i)) =
      ∑ i : Fin n, f ((toeplitz_isHermitian m n).eigenvalues i) := by
  classical
  have hlist : List.ofFn (orderedEigenvalue m n) = orderedEigenvalueList m n := by
    apply List.ext_getElem
    · simp [length_orderedEigenvalueList]
    · intro i hi hj
      simp only [List.getElem_ofFn]
      rfl
  have hmulti : (orderedEigenvalueList m n : Multiset ℝ) =
      (List.ofFn (toeplitz_isHermitian m n).eigenvalues : Multiset ℝ) := by
    simp only [orderedEigenvalueList, Multiset.sort_eq]
  have hperm : (orderedEigenvalueList m n).Perm
      (List.ofFn (toeplitz_isHermitian m n).eigenvalues) := Multiset.coe_eq_coe.mp hmulti
  have hs := (hperm.map f).sum_eq
  rw [← hlist, List.map_ofFn, List.sum_ofFn, List.map_ofFn, List.sum_ofFn] at hs
  exact hs

theorem toeplitz_inverse_trace_ordered (m n : ℕ) (hm : 1 ≤ m) :
    Matrix.trace (toeplitz m n)⁻¹ = ∑ i : Fin n, (orderedEigenvalue m n i)⁻¹ := by
  rw [sum_orderedEigenvalue_map m n (fun x => x⁻¹)]
  exact posDef_inverse_trace n (toeplitz m n) (toeplitz_posDef m n hm)

theorem toeplitz_inverse_trace_one_based (m n : ℕ) (hm : 1 ≤ m) :
    Matrix.trace (toeplitz m n)⁻¹ = ∑ i : Fin n, 1 / eigenvalue m n (i.val + 1) := by
  rw [toeplitz_inverse_trace_ordered m n hm]
  apply Finset.sum_congr rfl
  intro i _
  rw [eigenvalue_in_range (by omega : 1 ≤ i.val + 1)
    (by omega : i.val + 1 ≤ n)]
  simp only [Nat.add_sub_cancel, one_div]

#print axioms posDef_inverse_trace
#print axioms sum_orderedEigenvalue_map
#print axioms toeplitz_inverse_trace_ordered
#print axioms toeplitz_inverse_trace_one_based

end MF21Restart
