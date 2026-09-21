# Scaled rising products and the kernel integrand

Locked 20 September 2026 before ScaledRising.lean.

Define the polynomial scaled rising product
`scaledRising r h x = product a<r, (x+a*h)` for natural r and real h,x.
Prove exact identities at h=0, at r+1, and

```
scaledRising r h (h*x) = h^r * (ascPochhammer Real r).eval x.
```

The scaling identity includes h=0 and r=0: it does not divide by h.
Prove continuity under continuous real substitutions and strict positivity
when h>=0 and x>0.

For natural m define

```
finiteKernelIntegrand m h x y t =
  scaledRising m h x * scaledRising m h y *
  scaledRising (m-1) h (t-x+h) * scaledRising (m-1) h (t-y+h) /
  (((m-1)!)^2 * scaledRising (2*m) h t).
```

At h=0 prove the exact rational-power integrand in manuscript (27):
`x^m*y^m*(t-x)^(m-1)*(t-y)^(m-1)/(((m-1)!)^2*t^(2*m))`.
The real division is totalized; no claim at a zero denominator will be used
for the integral.

On the compact parameter box h,x,y in [0,1], t in [1/4,1], prove continuity,
uniform continuity and a finite uniform absolute bound for this actual
integrand. The denominator is strictly positive throughout the box for
every natural m, by the factorial and rising-product positivity. This
allows the limit h->0 and parameter-uniform Riemann sums without interval
subdivision or any matrix-size computation. It does not yet identify the
rescaled matrix inverse with a Riemann sum or establish kernel convergence.
