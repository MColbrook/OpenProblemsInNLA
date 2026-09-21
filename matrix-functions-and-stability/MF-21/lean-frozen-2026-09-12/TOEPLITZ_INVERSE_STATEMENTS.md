# Actual inverse matrix from the finite weighted factorization

Locked 20 September 2026 before ToeplitzInverse.lean.

All matrices are indexed by Fin n, and A is the existing integral-defined
`toeplitz m n`. The mathematical range is m>=1 and any natural n, including
the empty matrix. Let P and W be the existing `risingFactorialDiagonal`
matrices of orders m and 2*m, and B be the existing `binomialUpperMatrix`.
Define V by the entrywise reciprocals of the diagonal entries of W.

Prove, without additional assumptions,

```
A * (P*B*V*B.transpose*P) = 1,
A⁻¹ = P*B*V*B.transpose*P.
```

Use positivity of rising factorials at the positive one-based indices i+1,
the exact two-sided triangular inverses, and the actual weighted Toeplitz
factorization. The generic inverse-algebra lemma's hypotheses must all be
discharged here. No desired eigenvalue or kernel estimate is a premise.

Extract every actual inverse entry as the finite sum

```
(A⁻¹)ij = (i+1)_m * (j+1)_m *
  sum k:Fin n,
    if i.val<=k.val and j.val<=k.val then
      choose(m-1+k.val-i.val,m-1) *
      choose(m-1+k.val-j.val,m-1) / (k+1)_(2*m)
    else 0.
```

Here the first choose upper index is precisely
`m-1+(k.val-i.val)` and the second analogously; all natural coefficients
are cast to Real. The rising-factorial arguments are real casts plus 1.
The inequalities prevent truncated natural subtraction from contributing
out-of-range terms. This is the exact finite inverse, not the uniform
asymptotic limit. Rewriting choose coefficients as rising factorials and
proving that limit remain separate obligations.
