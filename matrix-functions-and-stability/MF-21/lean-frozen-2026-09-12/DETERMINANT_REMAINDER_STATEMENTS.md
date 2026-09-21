# Determinant remainder: locked statements

20 September 2026, before writing `DeterminantRemainder.lean`.
This assembles the literal finite expression into manuscript Lemma 3.
It uses the existing roots, integral Toeplitz eigenvalues, actual boundary
determinant, and sum-of-individual-arguments phase without redefining any.

For every m>=2 and natural n, prove on 0<theta<=pi that

```
manuscriptNormalizedDeterminant m n theta
  = (Real.sin (manuscriptPhaseFn m n theta) : Complex)
      + boundaryErrorExpression m n hm theta.
```

This must follow by partitioning the actual finite Laplace expansion into
the two distinct leading subsets and all remaining cardinality-m subsets,
using their already proved exact normalization identities. It is not a
definition of the remainder or an assumption about the determinant.

Define `manuscriptError m n hm theta` as the real part of the existing
`boundaryErrorExpression`. Prove that its complex embedding equals that
expression on 0<theta<=pi, using the proved reality of the normalized
determinant. The finite expression is already regular on [0,pi], so the
real function is regular there as well.

The eigenvalue equivalence is required on the open interval only:

```
(exists j, 1 <= j and j <= n and eigenvalue m n j = symbol m theta)
  iff Real.sin (manuscriptPhaseFn m n theta) + manuscriptError m n hm theta = 0.
```

Uniform estimates must have constants chosen before n and theta:

```
exists c C > 0, forall n, forall theta in [0,pi],
 |E_n(theta)| <= C*exp(-c*n*theta)
 and |deriv E_n theta| <= C*(n+1)*exp(-c*n*theta).
```

Finally prove `E_n(pi)=0` from the literal colliding boundary columns and
`F_n(pi)=(n+1)*pi`, and with the same or enlarged positive constants prove

```
|E_n(theta)| <= C*(n+1)*(pi-theta)*exp(-c*n*pi/2)
    for pi/2 <= theta <= pi.
```

The endpoint estimate follows from the derivative bound and mean value
theorem, not from numerical interval subdivision. Constants depend only on
m. The result is precisely the determinant-error part of the manuscript;
it does not assert eigenvalue indexing, the all-orders implicit expansion,
the inverse-kernel trace limit, or the final MF-21 Target.
