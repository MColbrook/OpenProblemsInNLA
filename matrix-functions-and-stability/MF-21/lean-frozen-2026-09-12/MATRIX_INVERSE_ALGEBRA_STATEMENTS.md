# Exact inverse algebra from verified finite factors

Locked 20 September 2026 before MatrixInverseAlgebra.lean.

This is a symbolic finite-matrix helper for the known inverse formula used
to establish the manuscript's external inverse-kernel input. It is not
itself a Toeplitz theorem, kernel convergence statement, or MF-21 target.

For arbitrary real square matrices A, P, R, T, B, W, V on any finite index
type, assume only the explicit finite identities

```
R*P=1, T*B=1, B*T=1, W*V=1, T.transpose*W*T=P*A*P.
```

Prove the actual right inverse identity

```
A*(P*B*V*B.transpose*P)=1
```

and hence the equality with Mathlib's actual nonsingular matrix inverse

```
A⁻¹=P*B*V*B.transpose*P.
```

No desired spectral result is an assumption. All five finite hypotheses
must be discharged for the actual Toeplitz matrix in the subsequent module.
The proof is associativity, the four product identities, and transpose
reversal, with no computation depending on n or m.

Also prove that a diagonal matrix with entries w(i) and its entrywise
reciprocal diagonal are two-sided inverses when every w(i) is nonzero.
The empty index type is included; no nonempty hypothesis is necessary.
