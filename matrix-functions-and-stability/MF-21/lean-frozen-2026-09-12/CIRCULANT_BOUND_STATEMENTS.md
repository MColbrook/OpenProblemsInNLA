# Statement lock: actual one-based eigenvalue bounds (21)–(22)

Locked before source on 20 September 2026. All statements use the unchanged
`toeplitz`, `eigenvalue`, actual Fourier circulant, and its proved increasing
spectrum. No spectral formula or interlacing is an extra premise.

For m>=1, 1<=j<=n, and N=n+2m, prove

```
circulantOrderedValue m N j <= eigenvalue m n j
  <= circulantOrderedValue m N (j+2m).
```

This must instantiate the actual Hermitian principal-block theorem with
the already proved literal block equality. Its eigenbasis enumeration
must be identified with the unchanged sorted Toeplitz list, and the
circulant enumeration with the proved paired frequency list. The index
conversion is from zero-based j-1 to the manuscript's one-based j.

Using sine inequalities only on the proved half-frequency interval
`[0,pi/2]`, deduce

```
(4*((j/2 : Nat) : Real)/(n+2m))^(2m) <= eigenvalue m n j,
eigenvalue m n j <= (pi*(j+2m)/(n+2m))^(2m).
```

For j>=2, use `j/3<=floor(j/2)` to deduce

```
(4*j/(3*(n+2m)))^(2m) <= eigenvalue m n j.
```

The lower bound at j=1 is zero and is not strengthened. Repeated circulant
frequencies remain present in the preceding interlacing proof.

Expose the two required actual consequences:

1. For every fixed m>=1 and natural J, there exist C>0 and N0 such that
   for all n>=N0 and 1<=j<J with j<=n,
   `|eigenvalue m n j| <= C*(1/(n+2))^(2m)`.
   One can take N0=1 and `C=(pi*(J+2m))^(2m)`, because n+2<=n+2m.
2. For m>=1, 2<=j<=n, prove the explicit reciprocal majorant
   `(1/(n+2))^(2m)/eigenvalue m n j
      <= (3*m/4)^(2m)*((j:Real)^(2m))^-1`.
   In particular expose a positive-C, eventual-n version with that exact
   summable j-power. The proof uses actual spectral positivity and
   `(n+2m)/(n+2)<=m`, not an assumed inverse asymptotic.

The first consequence supplies the finite-prefix estimate needed to
combine the same-family coefficient expansion with the actual high-index
error. The second supplies the tail majorant for the trace limit. This
module alone does not assert the completed expansion, trace contradiction,
or MF-21 target. Only the coordinator runs serialized local tests.
