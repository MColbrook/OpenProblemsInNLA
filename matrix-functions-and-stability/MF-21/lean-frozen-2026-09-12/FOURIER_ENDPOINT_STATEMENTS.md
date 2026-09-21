# Exact outer Fourier coefficients

Statement lock for MF21Restart/FourierEndpoint.lean, 20 September 2026.
The module imports the tested FourierStencil module and proves the following
for the concrete normalized Fourier integrals in Definitions.lean:

    theorem fourierCoeff_right_endpoint (m : ℕ) :
        fourierCoeff m (m : ℤ) = (-1 : ℝ) ^ m

    theorem fourierCoeff_left_endpoint (m : ℕ) :
        fourierCoeff m (-(m : ℤ)) = (-1 : ℝ) ^ m

    theorem fourierCoeff_right_endpoint_ne_zero (m : ℕ) :
        fourierCoeff m (m : ℤ) ≠ 0

    theorem fourierCoeff_left_endpoint_ne_zero (m : ℕ) :
        fourierCoeff m (-(m : ℤ)) ≠ 0

The quantifier includes m=0, when both endpoints are frequency zero and
the coefficient is 1. There are no root, matrix-size, or spectral-limit
hypotheses.

For the induction step, the proved coefficient recurrence at frequency
m+1 reduces to minus the coefficient at frequency m: the other two terms
vanish by the established support bound. Symmetry gives the negative
endpoint. The nonzero assertions then follow from the nonzero base -1.

Together with support, these results establish the exact outer nonzero
coefficients needed when normalizing the order-2m recurrence. They do not
yet identify finite Toeplitz eigenspaces with boundary-determinant kernels,
or establish any part of the asymptotic Target. No completed-problem count
or verification claim follows from writing this statement lock.
