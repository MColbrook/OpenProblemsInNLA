# Recurrence basis: statement first

Source: frozen manuscript, Section 2, the paragraph after equation (13).

For a complex linear recurrence `E` of order `d`, let `w : Fin d → ℂ`
be an injective list of roots of its characteristic polynomial. Every
solution `u : ℕ → ℂ` has exactly one coefficient vector `c` such that

`u k = ∑ i, c i * (w i)^k` for every natural `k`.

This must be proved from the recurrence and the nonsingular Vandermonde
matrix; the representation is not a hypothesis. The recurrence, roots,
and root hypotheses will later be instantiated from the actual Fourier
stencil of MF-21. This general lemma alone is not the eigenvalue criterion.

For any injective nonzero root list, if such a geometric sum vanishes on
`d` consecutive indices beginning at `a`, all its coefficients are zero.
This records the exact nondegeneracy needed when comparing recurrence
and finite-vector kernels.

Both statements include zero order without special assumptions. No
spectral asymptotic, norm bound, or assertion of the MF-21 target is
assumed.
