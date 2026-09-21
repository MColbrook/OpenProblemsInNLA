# Finite recurrence bridge: statement first

Source: the equivalence of the ghost-value criterion and the finite
eigenvalue equation in the paragraph after manuscript (13).

For any complex recurrence `E` of order `d`, a sequence satisfying its
recurrence equation at every index `k < N` agrees on `t < N+d` with the
unique full recurrence solution determined by its first `d` entries.
This must be proved by induction from the actual recurrence equations.

For `d=2*m`, a vector `v : Fin n → ℂ` is placed at the indices
`m,...,m+n-1` and extended by zero outside that interval. Prove that a
nonzero such vector satisfies the recurrence equation at all `k<n` if
and only if there is a nonzero full recurrence solution with zero ghost
entries at `0,...,m-1` and `n+m,...,n+2*m-1`.

The middle vector is recovered by restricting the sequence to `m+i`.
Its nonzero property must be proved, not inferred from an unproved
dimension assertion. Natural-index subtraction is guarded by the actual
middle-interval membership test. The recurrence is not yet specialized
to the Fourier coefficients; the ensuing finite-matrix identity remains
a separate obligation.
