# Actual inverse trace and all sorted eigenvalues

Locked before InverseSpectralTrace.lean, 20 September 2026.

For every real positive-definite n-by-n matrix, prove that the trace of
its actual inverse is the sum of reciprocals of all Hermitian eigenvalues.
Use the proved spectral theorem, the nonzero actual eigenvalues, and a
constructed right inverse under unitary conjugation. In particular do not
treat the totalized ring inverse of a singular diagonal vector as a
pointwise inverse without discharging nonvanishing.

Prove that sorting the actual Toeplitz eigenvalue list preserves sums of
any real function, with repetitions. Then specialize the preceding identity
to the actual matrix, first for orderedEigenvalue indexed by Fin n and then
for eigenvalue m n (i.val+1). All n are included; the n=0 sum is empty.

These are exact finite identities, not asymptotic estimates. No reciprocal
trace identity or desired spectral limit is assumed. They will connect (29)
to the dominated counting-measure passage in (31).
