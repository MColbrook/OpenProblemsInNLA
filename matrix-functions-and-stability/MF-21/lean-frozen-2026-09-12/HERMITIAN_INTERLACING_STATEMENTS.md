# Statement lock: actual Hermitian principal-block interlacing

Locked before source on 20 September 2026. This module discharges the
norm and quadratic-form identities of `DiagonalInterlacing.lean` for
actual real Hermitian matrices. It does not assume a min-max theorem.

For a real Hermitian `n` by `n` matrix A, define
`hermitianAscendingValue A hA` by reversing the genuinely decreasing
eigenvalue enumeration of `A.toEuclideanLin` in the pinned Mathlib spectral
theorem. Prove it is monotone and that its `List.ofFn` is exactly the
increasing multiset sort of `hA.eigenvalues`, including multiplicities.
Thus this helper enumeration cannot change the original Toeplitz spectrum.

Use the correspondingly reversed orthonormal eigenbasis to define an
actual linear coordinate equivalence on `Fin n -> Real`. Prove that its
coordinates preserve the sum of squares and diagonalize the actual
quadratic form `sum_i (A.mulVec x i)*x i`. These are consequences of the
spectral theorem and inner-product preservation, with no new premise.

For n<=N and the explicit leading-index map `e=Fin.castLE hnN`, prove

```
sum_i f i * (initialCoordinateEmbedding n N hnN x i)
  = sum_j f (e j)*x j,
```

and the corresponding exact squared-norm and principal-block quadratic
identities. Extension by zero is literal; indices outside the leading
block contribute zero. No rank assumption or spectral estimate enters
these identities.

The main generic matrix theorem takes actual real Hermitian matrices A,B,
the actual equality `B.submatrix e e=A`, and `j:Fin n`. It proves

```
hermitianAscendingValue B hB (e j)
  <= hermitianAscendingValue A hA j,
hermitianAscendingValue A hA j
  <= hermitianAscendingValue B hB (j.val+(N-n)).
```

The linear map for the already proved diagonal-form theorem is precisely
ambient eigen-coordinates composed with extension by zero composed with
inverse principal-block eigen-coordinates. The norm identity and the form
identity must be proved from this definition. Empty n is allowed; repeated
eigenvalues are retained and only weak inequalities are asserted.

The subsequent circulant application will use the already proved actual
principal-block equality and actual sorted frequency list to obtain
manuscript (21)–(22) for the unchanged one-based `eigenvalue` definition.
This general matrix result is a necessary ingredient, not a completed
MF-21 target. Only the coordinator runs serialized local Lean tests.
