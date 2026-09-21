# General-order boundary determinant: selected statements

This module formalizes the actual determinant (13), then the grouped
column expansion that supplies (14). It is not a bound for raw roots assumed
to be contractive: exterior roots are allowed arbitrary modulus.

For `w : Fin (2*m) → ℂ`, define

    B(row,col) = w(col)^row,                 if row < m,
                 w(col)^(n+row),            otherwise.

Thus the exponents are exactly `0,...,m−1` and `n+m,...,n+2*m−1`.
Write `U(row,col)=w(col)^row` on the upper rows and zero below, and
`L(row,col)=w(col)^(row−m)` on the lower rows and zero above. Then

    B(row,col) = U(row,col) + w(col)^(n+m) * L(row,col).

For a subset S of columns, define C(S) as the determinant obtained by
selecting L's column at every index in S and U's column otherwise.
Multilinearity in columns gives the exact identity

    det B = sum_S C(S) * (prod_{i in S} w(i))^(n+m).

The coefficient C(S) is zero unless |S|=m. When |S|=m, arranging its
complement first and S last gives a block-diagonal matrix; its two block
determinants are the inherited-order Vandermonde determinants. The column
permutation contributes its actual sign. This recovers (14) without a
row/column permutation inversion ambiguity.

The initial implementation will establish the exact split and finite sum,
then the vanishing and minor identification. This does not yet prove the
spectral/kernel equivalence, the two leading terms (15), or the smoothly
normalized residual estimate (18). Those remain required steps, rather than
assumptions secretly counted as a completed determinant argument.

All identities are symbolic for arbitrary natural m,n; no enumeration over
matrix sizes, subsets, or permutations is used as a proof certificate.
