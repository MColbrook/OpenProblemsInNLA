# Toeplitz and zero-ghost convolution: statement first

Use the unchanged integral-defined `toeplitz m n` from Definitions.lean,
complexified entry by entry. For every `v : Fin n → ℂ` and `k : Fin n`,
prove that its matrix action at `k` is exactly

`∑ t : Fin (2*m+1), (fourierCoeff m (t-m) : ℂ) *
    zeroGhostExtension m n v (k+t)`.

The extension places `v_j` at the shifted manuscript index `m+j`.
The proof must derive omission of out-of-band terms from the actual
Fourier support theorem and must use the coefficient symmetry to match
the matrix's `k-j` convention with the convolution's `j-k` convention.
It must hold for all natural `m,n`, with no assumed eigenvalue equation.

This operator identity will allow the proved normalized Fourier
recurrence equation to match finite Toeplitz eigenvectors. It does not
alone identify or index eigenvalues, or prove the MF-21 target.
