import NLA.MF14Degree44.DegenerationIdentity
import NLA.MF14Degree44.CircuitSpanOperations
import Mathlib.Tactic.FinCases

/- Scalar-span algebra for Marcus Webb's degeneration. Formalization:
George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology; Codex assistance. No truncation is used
as a circuit operation. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
open scoped BigOperators
namespace NLA.MF14Degree44

lemma product_span_basis_mem (alpha eta gamma s : ℂ) (i : Fin 12) :
    productSpanBasis alpha eta gamma s i ∈ productSpan alpha eta gamma s := by
  exact Submodule.subset_span (Set.mem_range_self i)

lemma product_span_monomial_mem (alpha eta gamma s : ℂ) (k : Fin 7) :
    (X : Poly) ^ k.val ∈ productSpan alpha eta gamma s := by
  have hb := product_span_basis_mem alpha eta gamma s
    (⟨k.val, k.isLt.trans_le (by decide)⟩ : Fin 12)
  fin_cases k <;> simpa [productSpanBasis] using hb

lemma syzygy_basis_mem (alpha eta gamma s : ℂ) (i : Fin 5) :
    syzygyBasis alpha eta gamma s i ∈ productSpan alpha eta gamma s := by
  fin_cases i
  · exact product_span_basis_mem alpha eta gamma s 9
  · exact product_span_basis_mem alpha eta gamma s 7
  · exact product_span_basis_mem alpha eta gamma s 10
  · exact product_span_basis_mem alpha eta gamma s 11
  · exact product_span_basis_mem alpha eta gamma s 8

lemma degeneration_E_mem (alpha eta gamma s : ℂ) :
    degenerationE alpha eta gamma s ∈ productSpan alpha eta gamma s := by
  apply Submodule.sum_mem
  intro i _
  exact polynomial_C_mul_mem _ (syzygyCoefficients alpha eta gamma s i)
    (syzygy_basis_mem alpha eta gamma s i)

lemma low_part6_mem (alpha eta gamma s : ℂ) (p : Poly) :
    lowPart6 p ∈ productSpan alpha eta gamma s := by
  apply Submodule.sum_mem
  intro i _
  exact polynomial_C_mul_mem _ (p.coeff i.val)
    (product_span_monomial_mem alpha eta gamma s i)

theorem degeneration_in_span (alpha eta gamma s : ℂ) (hs : s ≠ 0) :
    degenerationZ alpha eta gamma s ∈ productSpan alpha eta gamma s := by
  have hsub := (productSpan alpha eta gamma s).sub_mem
    (degeneration_E_mem alpha eta gamma s)
    (low_part6_mem alpha eta gamma s (degenerationE alpha eta gamma s))
  rw [degeneration_identity] at hsub
  have hpos : C (s ^ 4) * degenerationZ alpha eta gamma s ∈ productSpan alpha eta gamma s := by
    simpa only [neg_neg] using (productSpan alpha eta gamma s).neg_mem hsub
  have hscaled := (productSpan alpha eta gamma s).smul_mem ((s ^ 4)⁻¹) hpos
  simpa only [smul_eq_C_mul, ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ (pow_ne_zero 4 hs), map_one, one_mul] using hscaled

#print axioms product_span_basis_mem
#assert_trust kernel product_span_basis_mem
#print axioms product_span_monomial_mem
#assert_trust kernel product_span_monomial_mem
#print axioms syzygy_basis_mem
#assert_trust kernel syzygy_basis_mem
#print axioms degeneration_E_mem
#assert_trust kernel degeneration_E_mem
#print axioms low_part6_mem
#assert_trust kernel low_part6_mem
#print axioms degeneration_in_span
#assert_trust kernel degeneration_in_span
end NLA.MF14Degree44
