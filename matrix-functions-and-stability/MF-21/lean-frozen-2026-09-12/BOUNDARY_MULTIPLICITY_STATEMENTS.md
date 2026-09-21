# Boundary multiplicity: statements before proof

Keep the actual integral-defined Toeplitz matrix and the same shifted ghost
indices as equation (13). For a valid list `w : Fin(2*m) → ℂ` of distinct
nonzero characteristic roots, define the linear interior evaluation map

```
I(c)(j) = sum_i c(i)*w(i)^(m+j),  j : Fin n.
```

Prove that restricting this map to the kernel of the actual boundary matrix
is a linear equivalence with the eigenspace of the complexified Toeplitz
matrix at `lam`. In particular, the two finite dimensions are equal.

The proof must construct both directions from the recurrence, not infer
multiplicity from the existing equivalence of nonzero-vector existence.
Finite recurrence extension supplies the inverse; uniqueness follows from
the two ghost blocks, the interior and the initial `2*m` values.

Hypotheses are `1 ≤ m`, injectivity and nonvanishing of `w`, and
`(2-w(i)-w(i)^(-1))^m=lam`. Actual root-list construction is separate.
The statement holds also for `n=0`. This does not yet prove that a zero of
the normalized determinant is simple or that its eigenangle has index `j`.
