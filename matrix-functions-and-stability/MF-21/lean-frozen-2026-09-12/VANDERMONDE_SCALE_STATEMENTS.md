# Statement lock: Vandermonde scaling

This component supplies the exact common vanishing power used after (18)
of the unchanged MF-21 manuscript. No quotient bound is a premise.

For `vandermondeDegree k = sum (i : Fin k), i.val`, prove
`2 * vandermondeDegree k = k * (k - 1)`.

For every complex list `u : Fin k -> Complex` and scalar `c`, prove
`det (vandermonde (fun i => 1 + c * u i)) =
c ^ vandermondeDegree k * det (vandermonde u)`.

Both statements include k=0 and k=1 and c=0. There is no distinctness
hypothesis and no division. The proof must use the actual determinant,
not a new surrogate definition of the Vandermonde.
