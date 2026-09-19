import NLA.MF14Degree44.ProductSpan
import Mathlib.LinearAlgebra.BilinearMap

/- Full span membership for the actual fourth-product map. Mathematics:
Marcus Webb, The University of Manchester. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology; Codex assistance. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
namespace NLA.MF14Degree44

def thirdInputBasis (alpha eta gamma s : ℂ) : Fin 5 → Poly :=
  ![1, X, X ^ 2, Q alpha, Rparam alpha eta gamma s]

def thirdInputSpan (alpha eta gamma s : ℂ) : Submodule ℂ Poly :=
  Submodule.span ℂ (Set.range (thirdInputBasis alpha eta gamma s))

lemma input_Q_mem_product_span (alpha eta gamma s : ℂ) :
    Q alpha ∈ productSpan alpha eta gamma s := by
  exact (productSpan alpha eta gamma s).add_mem
    (product_span_monomial_mem alpha eta gamma s 4)
    (polynomial_C_mul_mem _ alpha (product_span_monomial_mem alpha eta gamma s 3))

lemma input_XQ_mem_product_span (alpha eta gamma s : ℂ) :
    X * Q alpha ∈ productSpan alpha eta gamma s := by
  have h : (X : Poly) * Q alpha = X ^ 5 + C alpha * X ^ 4 := by unfold Q; ring
  rw [h]
  exact (productSpan alpha eta gamma s).add_mem
    (product_span_monomial_mem alpha eta gamma s 5)
    (polynomial_C_mul_mem _ alpha (product_span_monomial_mem alpha eta gamma s 4))

lemma input_X2Q_mem_product_span (alpha eta gamma s : ℂ) :
    X ^ 2 * Q alpha ∈ productSpan alpha eta gamma s := by
  have h : (X : Poly) ^ 2 * Q alpha = X ^ 6 + C alpha * X ^ 5 := by unfold Q; ring
  rw [h]
  exact (productSpan alpha eta gamma s).add_mem
    (product_span_monomial_mem alpha eta gamma s 6)
    (polynomial_C_mul_mem _ alpha (product_span_monomial_mem alpha eta gamma s 5))

lemma input_R_mem_product_span (alpha eta gamma s : ℂ) :
    Rparam alpha eta gamma s ∈ productSpan alpha eta gamma s := by
  let S := productSpan alpha eta gamma s
  have h2 : C (gamma * s) * X ^ 2 * Q alpha ∈ S := by
    rw [mul_assoc]
    exact polynomial_C_mul_mem S (gamma * s) (input_X2Q_mem_product_span alpha eta gamma s)
  exact S.add_mem (S.add_mem (S.add_mem
    (polynomial_C_mul_mem S (s ^ 2) (product_span_basis_mem alpha eta gamma s 7)) h2)
    (input_XQ_mem_product_span alpha eta gamma s))
    (polynomial_C_mul_mem S eta (product_span_monomial_mem alpha eta gamma s 3))

lemma third_input_basis_mem_product_span (alpha eta gamma s : ℂ) (i : Fin 5) :
    thirdInputBasis alpha eta gamma s i ∈ productSpan alpha eta gamma s := by
  fin_cases i
  · simpa [thirdInputBasis] using product_span_monomial_mem alpha eta gamma s 0
  · simpa [thirdInputBasis] using product_span_monomial_mem alpha eta gamma s 1
  · exact product_span_monomial_mem alpha eta gamma s 2
  · exact input_Q_mem_product_span alpha eta gamma s
  · exact input_R_mem_product_span alpha eta gamma s

lemma third_input_basis_products_mem (alpha eta gamma s : ℂ) (i j : Fin 5) :
    thirdInputBasis alpha eta gamma s i * thirdInputBasis alpha eta gamma s j ∈
      productSpan alpha eta gamma s := by
  fin_cases i <;> fin_cases j
  · simpa [thirdInputBasis, productSpanBasis, pow_succ, mul_assoc, mul_comm, mul_left_comm] using third_input_basis_mem_product_span alpha eta gamma s 0
  · simpa [thirdInputBasis, productSpanBasis, pow_succ, mul_assoc, mul_comm, mul_left_comm] using third_input_basis_mem_product_span alpha eta gamma s 1
  · simpa [thirdInputBasis, productSpanBasis, pow_succ, mul_assoc, mul_comm, mul_left_comm] using third_input_basis_mem_product_span alpha eta gamma s 2
  · simpa [thirdInputBasis, productSpanBasis, pow_succ, mul_assoc, mul_comm, mul_left_comm] using third_input_basis_mem_product_span alpha eta gamma s 3
  · simpa [thirdInputBasis, productSpanBasis, pow_succ, mul_assoc, mul_comm, mul_left_comm] using third_input_basis_mem_product_span alpha eta gamma s 4
  · simpa [thirdInputBasis, productSpanBasis, pow_succ, mul_assoc, mul_comm, mul_left_comm] using third_input_basis_mem_product_span alpha eta gamma s 1
  · simpa [thirdInputBasis, productSpanBasis, pow_succ, mul_assoc, mul_comm, mul_left_comm] using product_span_monomial_mem alpha eta gamma s 2
  · simpa [thirdInputBasis, productSpanBasis, pow_succ, mul_assoc, mul_comm, mul_left_comm] using product_span_monomial_mem alpha eta gamma s 3
  · simpa [thirdInputBasis, productSpanBasis, pow_succ, mul_assoc, mul_comm, mul_left_comm] using input_XQ_mem_product_span alpha eta gamma s
  · simpa [thirdInputBasis, productSpanBasis, pow_succ, mul_assoc, mul_comm, mul_left_comm] using product_span_basis_mem alpha eta gamma s 8
  · simpa [thirdInputBasis, productSpanBasis, pow_succ, mul_assoc, mul_comm, mul_left_comm] using third_input_basis_mem_product_span alpha eta gamma s 2
  · simpa [thirdInputBasis, productSpanBasis, pow_succ, mul_assoc, mul_comm, mul_left_comm] using product_span_monomial_mem alpha eta gamma s 3
  · simpa [thirdInputBasis, productSpanBasis, pow_succ, mul_assoc, mul_comm, mul_left_comm] using product_span_monomial_mem alpha eta gamma s 4
  · simpa [thirdInputBasis, productSpanBasis, pow_succ, mul_assoc, mul_comm, mul_left_comm] using input_X2Q_mem_product_span alpha eta gamma s
  · simpa [thirdInputBasis, productSpanBasis, pow_succ, mul_assoc, mul_comm, mul_left_comm] using product_span_basis_mem alpha eta gamma s 9
  · simpa [thirdInputBasis, productSpanBasis, pow_succ, mul_assoc, mul_comm, mul_left_comm] using third_input_basis_mem_product_span alpha eta gamma s 3
  · simpa [thirdInputBasis, productSpanBasis, pow_succ, mul_assoc, mul_comm, mul_left_comm] using input_XQ_mem_product_span alpha eta gamma s
  · simpa [thirdInputBasis, productSpanBasis, pow_succ, mul_assoc, mul_comm, mul_left_comm] using input_X2Q_mem_product_span alpha eta gamma s
  · simpa [thirdInputBasis, productSpanBasis, pow_succ, mul_assoc, mul_comm, mul_left_comm] using product_span_basis_mem alpha eta gamma s 7
  · simpa [thirdInputBasis, productSpanBasis, pow_succ, mul_assoc, mul_comm, mul_left_comm] using product_span_basis_mem alpha eta gamma s 10
  · simpa [thirdInputBasis, productSpanBasis, pow_succ, mul_assoc, mul_comm, mul_left_comm] using third_input_basis_mem_product_span alpha eta gamma s 4
  · simpa [thirdInputBasis, productSpanBasis, pow_succ, mul_assoc, mul_comm, mul_left_comm] using product_span_basis_mem alpha eta gamma s 8
  · simpa [thirdInputBasis, productSpanBasis, pow_succ, mul_assoc, mul_comm, mul_left_comm] using product_span_basis_mem alpha eta gamma s 9
  · simpa [thirdInputBasis, productSpanBasis, pow_succ, mul_assoc, mul_comm, mul_left_comm] using product_span_basis_mem alpha eta gamma s 10
  · simpa [thirdInputBasis, productSpanBasis, pow_succ, mul_assoc, mul_comm, mul_left_comm] using product_span_basis_mem alpha eta gamma s 11

lemma third_input_span_le_product_span (alpha eta gamma s : ℂ) :
    thirdInputSpan alpha eta gamma s ≤ productSpan alpha eta gamma s := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact third_input_basis_mem_product_span alpha eta gamma s i

lemma third_input_span_product_mem (alpha eta gamma s : ℂ) {u v : Poly}
    (hu : u ∈ thirdInputSpan alpha eta gamma s)
    (hv : v ∈ thirdInputSpan alpha eta gamma s) :
    u * v ∈ productSpan alpha eta gamma s := by
  apply LinearMap.BilinMap.apply_apply_mem_of_mem_span
    (productSpan alpha eta gamma s)
    (Set.range (thirdInputBasis alpha eta gamma s))
    (Set.range (thirdInputBasis alpha eta gamma s)) (LinearMap.mul ℂ Poly) _ u v hu hv
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  exact third_input_basis_products_mem alpha eta gamma s i j

/-- All three operands of the fourth map remain in any common available span. -/
lemma fourth_polynomial_operands (alpha eta gamma s lam : ℂ) (t : Fin 12 → ℂ)
    (S : Submodule ℂ Poly)
    (h1 : (1 : Poly) ∈ S) (hX : (X : Poly) ∈ S) (hX2 : (X : Poly) ^ 2 ∈ S)
    (hQ : Q alpha ∈ S) (hR : Rparam alpha eta gamma s ∈ S) :
    ∃ u v w : Poly, u ∈ S ∧ v ∈ S ∧ w ∈ S ∧
      fourthPolynomial alpha eta gamma s lam t = u * v + w := by
  let u := Rparam alpha eta gamma s + C (t 5) * X + C (t 6) * X ^ 2 + C (t 7) * Q alpha
  let v := Q alpha + C lam * X ^ 2 + C (t 8) * X + C (t 9) * X ^ 2 +
    C (t 10) * Q alpha + C (t 11) * Rparam alpha eta gamma s
  let w := C (t 0) + C (t 1) * X + C (t 2) * X ^ 2 +
    C (t 3) * Q alpha + C (t 4) * Rparam alpha eta gamma s
  have hu : u ∈ S := S.add_mem (S.add_mem (S.add_mem hR
    (polynomial_C_mul_mem S (t 5) hX)) (polynomial_C_mul_mem S (t 6) hX2))
    (polynomial_C_mul_mem S (t 7) hQ)
  have hv : v ∈ S := S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem hQ
    (polynomial_C_mul_mem S lam hX2)) (polynomial_C_mul_mem S (t 8) hX))
    (polynomial_C_mul_mem S (t 9) hX2)) (polynomial_C_mul_mem S (t 10) hQ))
    (polynomial_C_mul_mem S (t 11) hR)
  have ht0 : C (t 0) ∈ S := by simpa only [mul_one] using polynomial_C_mul_mem S (t 0) h1
  have hw : w ∈ S := S.add_mem (S.add_mem (S.add_mem (S.add_mem ht0
    (polynomial_C_mul_mem S (t 1) hX)) (polynomial_C_mul_mem S (t 2) hX2))
    (polynomial_C_mul_mem S (t 3) hQ)) (polynomial_C_mul_mem S (t 4) hR)
  exact ⟨u, v, w, hu, hv, hw, rfl⟩

lemma fourth_polynomial_mem_product_span (alpha eta gamma s lam : ℂ) (t : Fin 12 → ℂ) :
    fourthPolynomial alpha eta gamma s lam t ∈ productSpan alpha eta gamma s := by
  have h (i : Fin 5) : thirdInputBasis alpha eta gamma s i ∈ thirdInputSpan alpha eta gamma s :=
    Submodule.subset_span (Set.mem_range_self i)
  obtain ⟨u, v, w, hu, hv, hw, heq⟩ := fourth_polynomial_operands alpha eta gamma s lam t
    (thirdInputSpan alpha eta gamma s) (h 0) (h 1) (h 2) (h 3) (h 4)
  rw [heq]
  exact (productSpan alpha eta gamma s).add_mem
    (third_input_span_product_mem alpha eta gamma s hu hv)
    (third_input_span_le_product_span alpha eta gamma s hw)

#print axioms third_input_basis_products_mem
#assert_trust kernel third_input_basis_products_mem
#print axioms third_input_span_product_mem
#assert_trust kernel third_input_span_product_mem
#print axioms fourth_polynomial_operands
#assert_trust kernel fourth_polynomial_operands
#print axioms fourth_polynomial_mem_product_span
#assert_trust kernel fourth_polynomial_mem_product_span
end NLA.MF14Degree44
