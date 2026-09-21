# Concrete substitution route from (27) to (28)

This is an API and proof-plan inspection, not a compiled Lean result.
No existing Lean source was edited for this inspection.

The direct scalar lemma to prove is, for a natural k and 0<x<=1,

    (∫ t in x..1, (t-x)^k / t^(k+2))
      = (1-x)^(k+1) / (((k+1 : ℕ) : ℝ) * x).

The original manuscript needs k=2m-2 and x>=1/2. Proving it for all
positive x<=1 is a natural stronger elementary statement.

## Existing substitution API

Pinned Mathlib has the following theorem in
Mathlib/MeasureTheory/Integral/IntervalIntegral/IntegrationByParts.lean,
line 531:

    theorem intervalIntegral.integral_comp_mul_deriv
        {f f' g : ℝ → ℝ}
        (h : ∀ t ∈ Set.uIcc a b, HasDerivAt f (f' t) t)
        (h' : ContinuousOn f' (Set.uIcc a b))
        (hg : Continuous g) :
        (∫ t in a..b, (g ∘ f) t * f' t) =
          ∫ u in f a..f b, g u

Use:

    a = x
    b = 1
    f t = 1 - x/t
    f' t = x/t^2
    g u = u^k/x

This uses the manuscript's substitution directly. It does not require
constructing the inverse t=x/(1-u), establishing an image equality, or
using a measure-theoretic Jacobian theorem.

## Side conditions and identities

Rewrite Set.uIcc x 1 to Set.Icc x 1 using Set.uIcc_of_le.
Every t in this interval satisfies t>=x>0, hence t is nonzero.

The derivative follows from:

* hasDerivAt_const and hasDerivAt_id.
* HasDerivAt.div in Analysis/Calculus/Deriv/Inv.lean, line 173.
* HasDerivAt.const_sub in Analysis/Calculus/Deriv/Add.lean, line 434.

Indeed, d(x/t)/dt=-x/t^2 and d(1-x/t)/dt=x/t^2.
The derivative is continuous on [x,1] because its denominator is
nonzero there. The polynomial divided by the constant x is globally
continuous, so the theorem's hg is immediate.

For each t in the interval,

    (1-x/t) = (t-x)/t,
    (g ∘ f)(t) * f'(t)
      = ((1-x/t)^k/x) * (x/t^2)
      = (t-x)^k/t^(k+2).

The normalization uses x!=0 and t!=0. After rewriting with div_pow and
pow_add, field_simp/ring can prove the equality; it should not be
introduced as an assumed change-of-variables identity.

The endpoints are f(x)=0 and f(1)=1-x. The integral on the right is
evaluated using:

* intervalIntegral.integral_div in IntervalIntegral/Basic.lean, line 827.
* intervalIntegral.integral_pow in Analysis/SpecialFunctions/Integrals/Basic.lean,
  line 173.

They give

    (∫ u in 0..1-x, u^k/x)
      = ((1-x)^(k+1)-0^(k+1))/(((k+1 : ℕ) : ℝ)*x)
      = (1-x)^(k+1)/(((k+1 : ℕ) : ℝ)*x).

k+1 is positive, including k=0. The case x=1 is harmless: the integral
has equal endpoints and the final positive-power numerator is zero.

## Recovering the diagonal formula

For m>=1, natural arithmetic gives:

    (2m-2)+1 = 2m-1,
    (2m-2)+2 = 2m.

Substitute k=2m-2, multiply by x^(2m)/((m-1)!)^2, and cancel the
positive factor x. This yields

    x^(2m-1) (1-x)^(2m-1)
      / ((2m-1) ((m-1)!)^2),

which is exactly manuscript (28) on x>=1/2, the diagonal region where
the cited formula (27) applies directly.

For 0<=x<=1/2, use the separately established kernel reflection
G(x,x)=G(1-x,1-x). The reflected point is in [1/2,1], and the displayed
polynomial is reflection invariant. At x=0 this reduces to x=1,
so no substitution at the singular denominator x=0 is needed.

The kernel representation and reflection still need their own formal
connection to the cited Green kernel. This substitution lemma alone
does not prove the inverse-kernel limit or the finite-matrix trace limit.
