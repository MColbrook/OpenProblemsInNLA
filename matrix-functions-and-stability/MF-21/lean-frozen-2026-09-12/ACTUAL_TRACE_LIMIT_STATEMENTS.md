# The actual matrix trace limit (29)

Locked before ActualTraceLimit.lean, 20 September 2026.

For every fixed m>=1 prove both limits for the actual inverse matrix:

```
lim_n (1/n)^(2m) * Matrix.trace((toeplitz m n)^-1) = kernelTraceConstant m,
lim_n (1/(n+2))^(2m) * Matrix.trace((toeplitz m n)^-1) = kernelTraceConstant m.
```

Use the already proved uniform error at every actual grid point, including
the diagonal, to compare the trace with the right-grid average of G(x,x).
The average tends to its integral by continuous_grid_average_tendsto; the
actual diagonal integral equals the explicit positive rational constant.
The normalization change is the elementary factor (n/(n+2))^(2m)->1.

The proof must include the exact finite identity relating n^{-(2m)}
trace to n^{-1} times the sum of scaled inverse diagonal entries. The
uniform per-entry error then averages to the same error, not n times it.
No matrix trace convergence is assumed. This does not yet identify the
trace as a sum over reciprocal sorted eigenvalues or prove (31).
