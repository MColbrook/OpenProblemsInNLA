# A symbolic Riemann-sum error bound

Locked 20 September 2026 before RiemannCellBound.lean.

Let a:Nat->Real be monotone and L<=U. Let f:Real->Real be interval
integrable on every [a(k),a(k+1)] for L<=k<U. Suppose the oscillation from
the right endpoint satisfies

```
abs(f(a(k+1))-f(x)) <= epsilon
```

on each entire closed cell. Prove the finite, exact estimate

```
abs(sum_{k=L}^{U-1} (a(k+1)-a(k))*f(a(k+1))
    - integral_{a(L)}^{a(U)} f)
  <= epsilon*(a(U)-a(L)).
```

Permit L=U and repeated partition points. The proof sums the interval
integral of each cell error, applies the pointwise absolute bound, and
telescopes interval lengths. No numerical integration, asymptotic input,
or sampling-based inference is used. Uniform continuity of the concrete
kernel integrand will discharge the cell-oscillation premise later.
