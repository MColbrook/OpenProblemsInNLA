import NLA.MF14Degree44.FourthMinorCoefficients
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.FinCases
import LeanCert.Tactic.Verification

/- Sparse degree and leading coefficient facts; no matrix entry grid expands.
Mathematics: Marcus Webb. Formalization: George Stepaniants, Department of
Computing and Mathematical Sciences, California Institute of Technology;
Codex assistance. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
namespace NLA.MF14Degree44

lemma Q_square_degree_le (alpha : ℂ) : (Q alpha ^ 2).natDegree ≤ 8 := by
  exact (natDegree_pow_le_of_le 2 (fourth_Q_degree alpha)).trans (by decide)

lemma Q_square_coeff_eight (alpha : ℂ) : (Q alpha ^ 2).coeff 8 = 1 := by
  rw [pow_two]
  have h := coeff_mul_add_eq_of_natDegree_le (fourth_Q_degree alpha) (fourth_Q_degree alpha)
  simpa only [fourth_Q_coeff4, one_mul] using h

lemma product_span_basis_degree_le (alpha eta gamma s : ℂ) (i : Fin 12) :
    (productSpanBasis alpha eta gamma s i).natDegree ≤ (fourthRows i).val := by
  have hR := fourth_R_degree alpha eta gamma s
  have hQ := fourth_Q_degree alpha
  have hp (k : ℕ) : ((X : Poly) ^ k).natDegree ≤ k := by simp
  fin_cases i
  · simp [productSpanBasis, fourthRows]
  · simp [productSpanBasis, fourthRows]
  · exact hp 2
  · exact hp 3
  · exact hp 4
  · exact hp 5
  · exact hp 6
  · exact Q_square_degree_le alpha
  · change ((X : Poly) * Rparam alpha eta gamma s).natDegree ≤ 9
    exact natDegree_mul_le.trans (by simp only [natDegree_X]; omega)
  · change ((X : Poly) ^ 2 * Rparam alpha eta gamma s).natDegree ≤ 10
    exact natDegree_mul_le.trans (Nat.add_le_add (hp 2) hR)
  · exact natDegree_mul_le.trans (Nat.add_le_add hQ hR)
  · exact (natDegree_pow_le_of_le 2 hR).trans (by decide)

lemma product_span_basis_diagonal (alpha eta gamma s : ℂ) (i : Fin 12) :
    (productSpanBasis alpha eta gamma s i).coeff (fourthRows i).val =
      (![1,1,1,1,1,1,1,1,s^2,s^2,s^2,s^4] : Fin 12 → ℂ) i := by
  have hR := fourth_R_degree alpha eta gamma s
  have hQ := fourth_Q_degree alpha
  have hp (k : ℕ) : ((X : Poly) ^ k).natDegree ≤ k := by simp
  fin_cases i
  · simp [productSpanBasis, fourthRows]
  · simp [productSpanBasis, fourthRows]
  · simp [productSpanBasis, fourthRows]
  · simp [productSpanBasis, fourthRows]
  · simp [productSpanBasis, fourthRows]
  · simp [productSpanBasis, fourthRows]
  · simp [productSpanBasis, fourthRows]
  · exact Q_square_coeff_eight alpha
  · have h := coeff_mul_add_eq_of_natDegree_le (f := (X : Poly)) (by simp : (X : Poly).natDegree ≤ 1) hR
    simpa [productSpanBasis, fourthRows, fourth_R_coeff8] using h
  · have h := coeff_mul_add_eq_of_natDegree_le (hp 2) hR
    simpa [productSpanBasis, fourthRows, fourth_R_coeff8] using h
  · have h := coeff_mul_add_eq_of_natDegree_le hQ hR
    simpa [productSpanBasis, fourthRows, fourth_R_coeff8, fourth_Q_coeff4] using h
  · have h := coeff_mul_add_eq_of_natDegree_le hR hR
    change (Rparam alpha eta gamma s ^ 2).coeff 16 = s ^ 4
    rw [pow_two, h, fourth_R_coeff8]
    ring

#print axioms product_span_basis_degree_le
#assert_trust kernel product_span_basis_degree_le
#print axioms product_span_basis_diagonal
#assert_trust kernel product_span_basis_diagonal
end NLA.MF14Degree44
