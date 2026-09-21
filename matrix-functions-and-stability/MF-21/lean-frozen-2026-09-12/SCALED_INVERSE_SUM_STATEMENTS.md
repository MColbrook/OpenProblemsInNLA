# Exact scaled inverse as a finite Riemann sum

Locked 20 September 2026 before ScaledInverseSum.lean.

For m>=1, any n, any nonzero real h, and actual indices i,j:Fin n,
set x_i=h*(i.val+1). Prove the exact identity

```
h^(2*m-1) * ((toeplitz m n)⁻¹) i j =
  h * sum k:Fin n,
    if i.val<=k.val and j.val<=k.val then
      finiteKernelIntegrand m h x_i x_j x_k
    else 0.
```

The integrand is the existing concrete scaled-rising expression, with
the factorial normalization and both shifted differences t-x+h, t-y+h.
This is exact algebra for arbitrary h!=0; the later asymptotic application
will choose h=1/n. It uses the proven actual inverse formula and the
division-free scaling identity for every rising product. Natural
subtractions are converted to real differences only inside their guards.
No kernel limit, Riemann-sum convergence, or spectral asymptotic is assumed.
