# Exact entries and reflection for the inverse-kernel limit

Locked 20 September 2026 before InverseKernelEntries.lean.

For all natural r,d prove the real identity

```
choose(r+d,r) = (d+1)_r / r!.
```

Use it to rewrite the actual finite inverse (m>=1, all n) as

```
(A_n⁻¹)ij = (i+1)_m*(j+1)_m / ((m-1)!)² *
  sum k:Fin n,
    if i.val<=k.val and j.val<=k.val then
      (k.val-i.val+1)_(m-1)*(k.val-j.val+1)_(m-1)/(k+1)_(2*m)
    else 0.
```

The rises use real casts of natural differences plus 1; the guards ensure
they represent the ordinary differences. This is the known finite inverse
formula, established through the already checked actual weighted matrix
factorization, not a new mathematical attribution.

Also prove the exact reversal symmetry of the actual Toeplitz matrix and
its actual inverse: simultaneously replacing i,j by Fin.rev leaves each
entry unchanged. The matrix identity follows from its original even Fourier
coefficient, and the inverse identity follows from equivariant matrix
inversion. All n, including n=0, are permitted.

These results prepare the uniform kernel estimate. They do not assert that
estimate, diagonal convergence, or a limiting trace.
