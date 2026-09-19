/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial Codex assistance. Marcus Webb retains mathematical authorship.

Three actual products produce one shared tuple. The last product is followed
only by free complex linear combinations of already available polynomials.
-/
import NLA.MF14Degree44.CircuitSpanOperations
import NLA.MF14Degree44.ThirdProductFactorization

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
namespace NLA.MF14Degree44

theorem three_product_tuple (alpha eta gamma s : ℂ)
    (hdelta : gamma * s - 2 * s ^ 2 ≠ 0) :
    SimultaneouslyAvailable 3 (thirdTuple alpha eta gamma s) := by
  classical
  let q0 : NLA.MF14.GatePolynomials := fun _ => 0
  have hq0 : IsCircuitPrefix q0 0 := by
    refine ⟨by decide, ?_⟩
    intro k hk
    omega
  obtain ⟨q1, hq1, _, hx2raw⟩ :=
    append_product_to_prefix q0 (0 : Fin 7) hq0 X X
      (available_X q0 0) (available_X q0 0)
  have hx2 : (X : Poly) ^ 2 ∈ NLA.MF14.availableSpace q1 1 := by
    change (X : Poly) * X ∈ NLA.MF14.availableSpace q1 1 at hx2raw
    simpa only [pow_two] using hx2raw
  have hsecond : (X : Poly) ^ 2 + C alpha * X ∈ NLA.MF14.availableSpace q1 1 :=
    (NLA.MF14.availableSpace q1 1).add_mem hx2
      (polynomial_C_mul_mem _ alpha (available_X q1 1))
  obtain ⟨q2, hq2, h12, hQraw⟩ :=
    append_product_to_prefix q1 (1 : Fin 7) hq1
      (X ^ 2) (X ^ 2 + C alpha * X) hx2 hsecond
  have hQ : Q alpha ∈ NLA.MF14.availableSpace q2 2 := by
    have hQeq : Q alpha = (X : Poly) ^ 2 * (X ^ 2 + C alpha * X) := by
      unfold Q
      ring
    rw [hQeq]
    exact hQraw
  have hx2' : (X : Poly) ^ 2 ∈ NLA.MF14.availableSpace q2 2 := h12 hx2
  let g : ℂ := gamma * s - s ^ 2
  let sigma : ℂ := (eta - 1 + alpha * g) / (gamma * s - 2 * s ^ 2)
  let rho : ℂ := 1 - s ^ 2 * sigma
  have hsigma : (gamma * s - 2 * s ^ 2) * sigma =
      eta - 1 + alpha * (gamma * s - s ^ 2) := by
    exact mul_div_cancel₀ _ hdelta
  let u3 : Poly := C (s ^ 2) * Q alpha + C rho * X + C g * X ^ 2
  let v3 : Poly := Q alpha + C sigma * X + X ^ 2
  have hu3 : u3 ∈ NLA.MF14.availableSpace q2 2 :=
    (NLA.MF14.availableSpace q2 2).add_mem
      ((NLA.MF14.availableSpace q2 2).add_mem
        (polynomial_C_mul_mem _ (s ^ 2) hQ)
        (polynomial_C_mul_mem _ rho (available_X q2 2)))
      (polynomial_C_mul_mem _ g hx2')
  have hv3 : v3 ∈ NLA.MF14.availableSpace q2 2 :=
    (NLA.MF14.availableSpace q2 2).add_mem
      ((NLA.MF14.availableSpace q2 2).add_mem hQ
        (polynomial_C_mul_mem _ sigma (available_X q2 2))) hx2'
  have hfactor : Rparam alpha eta gamma s =
      u3 * v3 - C g * Q alpha - C (rho * sigma) * X ^ 2 := by
    exact third_product_factorization alpha (s ^ 2) (gamma * s) eta sigma hsigma
  obtain ⟨q3, hq3, h23, hproduct⟩ :=
    append_product_to_prefix q2 (2 : Fin 7) hq2 u3 v3 hu3 hv3
  have hR : Rparam alpha eta gamma s ∈ NLA.MF14.availableSpace q3 3 := by
    rw [hfactor]
    exact (NLA.MF14.availableSpace q3 3).sub_mem
      ((NLA.MF14.availableSpace q3 3).sub_mem hproduct
        (polynomial_C_mul_mem _ g (h23 hQ)))
      (polynomial_C_mul_mem _ (rho * sigma) (h23 hx2'))
  refine ⟨q3, hq3, ?_⟩
  intro i
  fin_cases i
  · change (X : Poly) ^ 2 ∈ NLA.MF14.availableSpace q3 3
    exact h23 hx2'
  · change Q alpha ∈ NLA.MF14.availableSpace q3 3
    exact h23 hQ
  · change Rparam alpha eta gamma s ∈ NLA.MF14.availableSpace q3 3
    exact hR

#print axioms three_product_tuple
#assert_trust kernel three_product_tuple
end NLA.MF14Degree44
