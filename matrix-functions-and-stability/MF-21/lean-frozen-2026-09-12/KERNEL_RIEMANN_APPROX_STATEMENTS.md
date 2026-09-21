# Uniform approximation of the concrete kernel integrand

Locked 20 September 2026 before KernelRiemannApprox.lean.

Use the already defined `finiteKernelIntegrand m h x y t` and its compact
parameter box h,x,y in [0,1], t in [1/4,1]. The natural m is fixed in each
theorem; no numerical subdivision or derivative constant is computed.

First expose membership of ![h,x,y,t] in that exact box. Prove that for
each positive epsilon there is a positive delta, independent of x,y,t,
such that 0<=h<=1 and h<delta imply

```
abs(F(m,h,x,y,t)-F(m,0,x,y,t)) < epsilon
```

throughout x,y in [0,1], t in [1/4,1]. Use the already proved compact
uniform continuity and the exact product-space coordinate distance.

Next prove uniform right-endpoint Riemann approximation: for every
epsilon>0 there is N>=1 such that for all n>=N, h,x,y in [0,1], and
natural a<=n with 1/4<=a/n,

```
abs((1/n)*sum_{k=a}^{n-1} F(m,h,x,y,(k+1)/n)
    - integral_{a/n}^1 F(m,h,x,y,t)) <= epsilon.
```

The entire family is uniform in h,x,y and the moving initial grid index a.
The case a=n is included. Cell lengths are exactly 1/n; compact uniform
continuity gives a uniform oscillation bound. Apply the already proved
symbolic cell-sum estimate and total interval length <=1.

This does not yet assert the original kernel limit: the actual inverse
sum's guard must be reindexed, h must be specialized to 1/n, the lower
integration endpoint shifted to max(x,y), and reflection/grid conventions
must still be proved. Those are separate obligations, not assumptions.
