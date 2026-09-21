# Statement lock: uniform Taylor expansion of the actual implicit symbol

Locked before source on 20 September 2026. The coordinator approved the
interface. The manuscript equation for Y is (4), the coefficients are
(5), and the uniform Taylor formula is (23). No manuscript change is
made.

Use the same actual implicit function Y and the positive constants
r, epsilon, C supplied by `manuscriptEta_uniform_implicit_phase`.
For all natural k and real x define the single family

```lean
implicitPhaseCoefficient m Y k x :=
  iteratedDeriv k (fun h : ℝ => symbol m (Y (x,h))) 0 /
    (k.factorial : ℝ)
```

This is the exact derivative/factorial formula in (5), with the actual
original symbol. It is not an arbitrary approximation family and has
no dependence on n, j, or the truncation order p. Its values outside
the x-neighborhood are a totalization only.

Prove the existence of positive r, epsilon, C, delta, with delta<epsilon,
and one Y that retains all five conclusions of the uniform implicit
phase theorem (joint analytic regularity, actual equation and range,
displacement bound, initial value, and fixed-interval uniqueness), and
also has the following properties:

1. For each natural k, `implicitPhaseCoefficient m Y k` is
   `ContDiffAt Real ⊤` at every x in `Ioo (-r/2) (pi+r/2)`.
2. On that same interval, `implicitPhaseCoefficient m Y 0 x=symbol m x`.
3. For every natural p there exists `Cp>0` such that for every
   `x in Icc 0 pi` and every real h with `|h|<=delta`,

   ```
   |symbol m (Y (x,h))
      - sum k in range(p+1), implicitPhaseCoefficient m Y k x * h^k|
       <= Cp * |h|^(p+1).
   ```

The same delta, Y, and coefficient family work for all p. Cp is chosen
after p, before x or h. Both positive and negative h and both endpoints
x=0,pi are included. The value h=0 is checked explicitly.
The exact order `⊤ : ℕ∞ω` is analytic omega in this Mathlib; it implies
the required smooth regularity and is not confused with order infinity.

Before its source, the permitted helper `ParametricTaylor.lean` is
fixed as follows. For an actual function F of two real variables define
its vertical k-th derivative by the literal iterated one-variable
derivative of `h -> F(x,h)` at h. Prove joint analytic regularity of
that function from joint analytic regularity of F, using the library's
parametric `ContDiffAt.fderiv` and continuous-linear evaluation. This
supplies regularity of the exact coefficient functions.

For F analytic at every point of the open rectangle
`(-r/2,L+r/2) × (-epsilon,epsilon)`, where L>=0 and r,epsilon>0,
prove the displayed uniform Taylor bound on `[0,L]` with the exact
derivative/factorial coefficients. Choose delta=epsilon/2, bound the
(p+1)-st vertical derivative by compactness on
`[0,L] × [-delta,delta]`, and apply the pinned library
`taylor_mean_remainder_lagrange_iteratedDeriv` to each h-section.
Convert all within-interval Taylor coefficients at zero to unrestricted
iterated derivatives using actual regularity. A derivative bound is
derived, not included as an extra final hypothesis.

The actual module `ImplicitTaylor.lean` instantiates this helper with
`F(x,h)=symbol m (Y(x,h))`, proving its joint regularity from the actual
symbol and the constructed Y. All generic helper assumptions must be
discharged. No coefficient family or Taylor conclusion may be assumed.

The coefficient vanishing estimates (24), extension independence of
the coefficients, and comparison with actual eigenvalues remain
separate necessary obligations. This component alone does not prove
the full expansion target, the sharp threshold, or complete MF-21.
The author runs no compiler; the coordinator retains exact local
serial test evidence. Comparator remains a separate final check.
