# Statement lock: actual coefficient vanishing, manuscript (24)

Locked before source on 20 September 2026. The coordinator approved the
power-factor route. The exact family is the existing definition
`implicitPhaseCoefficient m Y k x`, the iterated h-derivative of the
actual `symbol m (Y(x,h))` at zero divided by k!. No new approximation
family or manuscript change is allowed.

The bounded generic component `VerticalPowerFactor.lean` defines
analytic factors for a function `u : Real × Real -> Real` and a natural N:

```
A_0(p) = 1
A_(k+1)(p) = (N-k) * verticalIteratedDeriv u 1 p * A_k(p)
              + u(p) * verticalIteratedDeriv A_k 1 p.
```

Here N-k is natural subtraction cast to Real. The claim is used only
with k<=N. Prove that every A_k is jointly analytic wherever u is,
and prove the exact identity

```
verticalIteratedDeriv (fun p => u p ^ N) k p
  = u p ^ (N-k) * A_k(p)
```

for k<=N and `ContDiffAt Real ⊤ u p`. Repeated h-differentiation,
the ordinary product and power rules, and equality on a neighborhood
must prove the identity; no vanishing identity is an assumption.
The analytic order top=omega permits analytic regularity in a common
neighborhood when differentiating the inductive identity.

The exact actual-function helper in `CoefficientVanishing.lean` takes
any Y with the already proved joint analytic regularity on
`(-r/2,pi+r/2) × (-epsilon,epsilon)`, r,epsilon>0, and with
`Y(x,0)=x` for x in [0,pi]. It proves

```lean
∀ k : ℕ, k ≤ 2*m → ∃ Ck : ℝ, 0 < Ck ∧
  ∀ x ∈ Set.Icc (0 : ℝ) Real.pi,
    |implicitPhaseCoefficient m Y k x| ≤ Ck * x^(2*m-k)
```

This includes k=0, k=2m, x=0, and x=pi with no limiting convention
inserted. For k=2m the power is x^0=1. The radius, Y, and coefficient
family are not allowed to vary with k. Ck may depend on the fixed m,Y
and k, but not on x or h.

Use the actual `u(x,h)=2*sin(Y(x,h)/2)` and N=2m, for which u^N
is literally the original symbol composed with Y. Apply the proved
factor identity at (x,0). Joint analyticity makes A_k(x,0) continuous
on the compact x-interval and thus uniformly bounded. The exact
initial value gives u(x,0)=2*sin(x/2), and `|sin t|<=|t|` gives
`|u(x,0)|<=x` for x>=0. Taking powers, multiplying the factor bound,
and dividing by the positive factorial proves the displayed estimate.
Thus the zero order is established by actual differentiation of the
power, not by assuming (24) or using an unknown coefficient formula.

Finally `manuscript_uniform_implicit_taylor_with_vanishing` will apply
this helper to the one actual Y of `manuscript_uniform_implicit_taylor`.
It retains all of that theorem's existential constants and conclusions
(actual eta equation, uniqueness, size bound, analytic coefficient
family, d0=symbol, common-delta all-order uniform remainder) and appends
the displayed vanishing bounds for the same Y and same family.
Every helper assumption is discharged by the earlier constructed Y.

The extension-independence statement and final spectral assembly remain
explicitly unproved by this component. This is not the full expansion,
threshold obstruction, uniform inverse-kernel limit, or MF-21 target.
Only the coordinator runs the serialized local Lean tests and records
their actual source-matched evidence; Comparator is separate.
