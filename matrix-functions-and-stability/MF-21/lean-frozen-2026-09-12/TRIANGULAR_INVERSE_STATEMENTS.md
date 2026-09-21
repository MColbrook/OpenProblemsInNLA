# Finite triangular factors from power-series coefficients

Locked 20 September 2026 before `TriangularInverse.lean`.
This is a bounded algebraic component needed to formalize the known inverse
formula underlying the manuscript's cited kernel convergence input. It does
not change the manuscript or assume that convergence or any spectral limit.

For f in the formal power-series ring over the reals define an n by n matrix
on zero-based Fin n indices by

```
powerSeriesUpperMatrix n f i j =
  if i.val <= j.val then coeff (j.val-i.val) f else 0.
```

Prove that this map sends 1 to the identity matrix and sends f*g to the
actual matrix product of the two images. This requires exact reindexing of
the coefficient convolution; no truncation of an infinite analytic series
or convergence argument is involved. The only relevant indices are
i<=k<=j<n. The n=0 case is allowed and vacuous entrywise.

Use the pinned Mathlib unit `PowerSeries.invOneSubPow Real m` to define
`binomialUpperMatrix m n` from its value, and `differenceUpperMatrix m n`
from `(1-X)^m`. Prove both matrix products equal the identity for every
natural m,n. The required unit inverse identity is already a library theorem,
`invOneSubPow_inv_eq_one_sub_pow`; do not assume a matrix inverse formula.

Expose the actual entries, for all i,j:Fin n:

```
B_ij = if i.val<=j.val
       then choose(m-1+(j.val-i.val), m-1) else 0    (m>=1),
T_ij = if i.val<=j.val
       then (-1)^(j.val-i.val)*choose(m,j.val-i.val) else 0.
```

The sign in T is fixed to the column-minus-row offset. All choose values
are cast to Real. The B formula needs m>=1; the definitions and inverse
identities include m=0, when both matrices are identities. The power-series
coefficient formula for T follows by rescaling X to -X in `(1+X)^m` and
using the polynomial binomial coefficient theorem. This avoids separate
alternating-binomial summation infrastructure and numerical computation.

The weighted-factorial diagonal, actual Fourier Toeplitz identification,
inverse entries, and uniform kernel limit remain separate obligations.
Completing this component does not complete MF-21.
