import MF21.BoundaryPolynomial
import MF21.BoundarySpectrum
import MF21.BulkRootFamily

/-! The boundary determinant for the actual MF-21 characteristic roots. -/
noncomputable section
open scoped BigOperators
namespace MF21ActualBoundary

/-- The fully constructed roots, transported to the recurrence's index type. -/
def roots (m : ℕ) (theta : ℝ) : Fin (2*m) → ℂ :=
  fun j => MF21Bulk.characteristicRoots m theta (Fin.cast (Nat.two_mul m) j)

theorem roots_injective (m : ℕ) (hm : 0 < m) (theta : ℝ)
    (ht : 0 < theta) (htp : theta < Real.pi) : Function.Injective (roots m theta) := by
  intro i j hij
  have h := MF21Bulk.characteristicRoots_injective m hm theta ht htp hij
  exact Fin.ext (congrArg (fun k : Fin (m+m) => k.val) h)

theorem symbol_eq_spectralBase (m : ℕ) (theta : ℝ) :
    (MF21Challenge.symbol m theta : ℂ) = (MF21Bulk.spectralBase theta : ℂ)^m := by
  rw [← Complex.ofReal_pow]
  congr 1
  unfold MF21Challenge.symbol MF21Bulk.spectralBase
  rw [pow_mul]

theorem roots_charPoly (m : ℕ) (hm : 0 < m) (theta : ℝ)
    (ht : 0 < theta) (htp : theta < Real.pi) (j : Fin (2*m)) :
    (MF21Boundary.recurrence m (MF21Challenge.symbol m theta)).charPoly.IsRoot
      (roots m theta j) := by
  have h := MF21Bulk.characteristicRoots_spec m hm theta ht htp (Fin.cast (Nat.two_mul m) j)
  apply (MF21Boundary.charPoly_root_iff_laurent m hm _ _ h.1).mpr
  rw [symbol_eq_spectralBase]
  exact h.2

/-- The unnormalized, exact ghost-value determinant for the actual symbol. -/
def determinant (m n : ℕ) (theta : ℝ) : ℂ :=
  (MF21Boundary.boundaryMatrix m n (roots m theta)).det

/-- The determinant has a zero exactly at an eigenvalue of the actual
complexified Toeplitz matrix. Its root hypotheses have all been discharged. -/
theorem eigenvector_iff_determinant_zero (m n : ℕ) (hm : 0 < m) (theta : ℝ)
    (ht : 0 < theta) (htp : theta < Real.pi) :
    (∃ v : Fin n → ℂ, v ≠ 0 ∧
      (MF21Boundary.toeplitz m n).mulVec v = (MF21Challenge.symbol m theta : ℂ) • v) ↔
      determinant m n theta = 0 :=
  MF21Boundary.eigenvector_iff_boundary_det_zero m n hm _ (roots m theta)
    (roots_injective m hm theta ht htp) (roots_charPoly m hm theta ht htp)


/-- The exact determinant criterion for the actual indexed real eigenvalues. -/
theorem sorted_eigenvalue_iff_determinant_zero (m n : ℕ) (hm : 0 < m)
    (theta : ℝ) (ht : 0 < theta) (htp : theta < Real.pi) :
    (∃ j : Fin n, MF21Challenge.eigenvalue m n j = MF21Challenge.symbol m theta) ↔
      determinant m n theta = 0 :=
  MF21Boundary.sorted_eigenvalue_iff_boundary_det_zero m n hm _ (roots m theta)
    (roots_injective m hm theta ht htp) (roots_charPoly m hm theta ht htp)

end MF21ActualBoundary
#print axioms MF21ActualBoundary.roots_charPoly
#print axioms MF21ActualBoundary.eigenvector_iff_determinant_zero

#print axioms MF21ActualBoundary.sorted_eigenvalue_iff_determinant_zero
