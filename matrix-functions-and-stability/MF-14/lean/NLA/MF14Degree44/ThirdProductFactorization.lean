/- Exact factorization from Marcus Webb's degree44 construction.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; substantial Codex assistance. -/
import NLA.MF14Degree44.Definitions
import Mathlib.Tactic.LinearCombination
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
namespace NLA.MF14Degree44

theorem third_product_factorization (alpha a b eta sigma : ℂ)
    (hsigma : (b - 2 * a) * sigma = eta - 1 + alpha * (b - a)) :
    C a * Q alpha ^ 2 + C b * X ^ 2 * Q alpha + X * Q alpha + C eta * X ^ 3 =
      (C a * Q alpha + C (1 - a * sigma) * X + C (b - a) * X ^ 2) *
        (Q alpha + C sigma * X + X ^ 2) -
      C (b - a) * Q alpha - C ((1 - a * sigma) * sigma) * X ^ 2 := by
  have hc := congrArg (Polynomial.C : ℂ → Poly) hsigma
  simp only [Q, map_sub, map_add, map_mul, map_ofNat, map_one] at hc ⊢
  linear_combination -X ^ 3 * hc

#print axioms third_product_factorization
#assert_trust kernel third_product_factorization
end NLA.MF14Degree44
