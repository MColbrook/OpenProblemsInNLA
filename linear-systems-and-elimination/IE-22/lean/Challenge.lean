import Definitions

set_option autoImplicit false

namespace IE22

/- Complete approved target: eventual uniform upper bound, optimality, and
   convergence of the extremal supremum along every high-aspect-ratio regime. -/
axiom full_result
    (theta : ℝ) (hθ : 0 < theta ∧ theta < 1)
    (a : ℝ) (ha : GaussianQuantile theta a) :
    EventualUniformUpper theta (cTheta theta a) ∧
    NoSmallerUniformConstant theta (cTheta theta a) ∧
    SupremumConverges theta (cTheta theta a)

#print axioms full_result

end IE22
