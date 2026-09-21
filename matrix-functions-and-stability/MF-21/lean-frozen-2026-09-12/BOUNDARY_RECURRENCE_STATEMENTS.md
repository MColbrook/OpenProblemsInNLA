# Boundary determinant and recurrence: statement first

Frozen manuscript: equation (13) and the paragraph immediately following it.

Let `E` be a complex linear recurrence of order `2*m`. Let
`w : Fin (2*m) → ℂ` be an injective nonzero list of roots of `E.charPoly`.
For the exact `boundaryMatrix m n w` already defined, prove that its
determinant vanishes if and only if there is a nonzero solution `u` of `E`
satisfying `u k = 0` and `u (n+m+k) = 0` for every `k : Fin m`.

The root representation is to be supplied by `RecurrenceBasis.lean`, not
assumed. The two ghost ranges must remain `0,...,m-1` and
`n+m,...,n+2*m-1`; these are the original manuscript indices after its
specified shift.

This is the recurrence part of the boundary criterion. The specialization
of `E` to the Fourier stencil and the bijection between ghost-constrained
solutions and finite Toeplitz eigenvectors remain explicit later
obligations. This statement makes neither spectral nor asymptotic claims.
