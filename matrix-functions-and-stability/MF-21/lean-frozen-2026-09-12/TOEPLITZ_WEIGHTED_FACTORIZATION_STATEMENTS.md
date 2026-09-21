# Statement lock: weighted factorization of the actual Toeplitz matrix

Locked before writing `MF21Restart/ToeplitzWeightedFactorization.lean` on
20 September 2026. This uses the unchanged integral coefficient and
Toeplitz definition, the proved weighted binomial identity, and the
separately developed Fourier and upper triangular matrix bridges.

For natural r,n define the diagonal matrix

```lean
def risingFactorialDiagonal (r n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i =>
    (ascPochhammer ℝ r).eval ((i.val : ℝ) + 1))
```

The natural index is shifted to the positive one-based argument i.val+1;
there is no evaluation at the zero root of the Pochhammer polynomial.
Prove exactly

```lean
theorem toeplitz_weighted_factorization (m n : ℕ) (hm : 1 ≤ m) :
    (differenceUpperMatrix m n).transpose *
        risingFactorialDiagonal (2 * m) n * differenceUpperMatrix m n =
      risingFactorialDiagonal m n * toeplitz m n * risingFactorialDiagonal m n
```

Here `differenceUpperMatrix m n` is the actual matrix defined from formal
power-series coefficients in `TriangularInverse.lean`; its entry is zero
unless row<=column, and then equals
`(-1)^(column-row)*choose(m,column-row)`. Thus the factorization is
literally `T^T W T=P A P`, not one with the transpose on the other side.
All matrices are n by n over the reals. Any n, including n=0, is allowed.
No inverse, invertibility, positive-definiteness or limiting assertion
is a hypothesis of this identity.

The entrywise proof for zero-based i>=j reduces its left side to

```
(-1)^(i-j) * sum_{k=1}^{j+1}
  choose(m,i+1-k)*choose(m,j+1-k)*(k)_(2m).
```

Reindex exactly by k=the matrix summation index+1. The signs combine to
`(-1)^(i-j)` because `(i-a)+(j-a)=(i-j)+2*(j-a)` when a<=j<=i.
Apply `weightedBinomialInverse_identity m (i-j) (j+1)` to obtain

```
(-1)^(i-j) * (j+1)_m * (i+1)_m * choose(2m,m+i-j).
```

The actual Fourier formula gives
`fourierCoeff m (i-j)=(-1)^(i-j)*choose(2m,m+i-j)` on this ordered range.
For i-j<=m this follows from `fourierCoeff_shifted_binomial` with
t=m+(i-j), including both endpoints. For i-j>m, the existing Fourier
support theorem and the out-of-range binomial convention make both sides
zero. All natural subtractions are guarded by the stated index orders;
the frequency fed to `fourierCoeff` remains an integer difference.
Symmetry of the Gram matrix and `fourierCoeff_neg` give the other half
of the entries. No finite-dimensional sampling is used.

Private entry and reindexing helpers are permitted. This proves finite
algebra toward the known Duduchava–Roch inverse factorization and keeps
its attribution. It is not yet a formula for an inverse entry, a uniform
kernel limit, or the complete MF-21 target. The source author runs no
compiler; the coordinator controls source-matched serial local tests
with one thread and 4096 MiB. Comparator remains a separate final check.
