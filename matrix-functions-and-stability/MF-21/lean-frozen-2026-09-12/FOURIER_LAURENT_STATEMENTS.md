# Finite Laurent identity

Statement lock for MF21Restart/FourierLaurent.lean, 20 September 2026.
This is the optional identity already specified before proof in
FOURIER_STENCIL_STATEMENTS.md. The separate module imports FourierStencil
so that the completed stencil source can remain frozen.

In namespace MF21Restart, prove exactly:

    theorem fourierCoeff_laurent_sum (m : ℕ) (z : ℂ) (hz : z ≠ 0) :
        (∑ k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
          (fourierCoeff m k : ℂ) * z ^ k) =
        (2 - z - z⁻¹) ^ m

The coefficients are still the normalized, concrete Fourier integrals in
Definitions.lean. Integer powers are used on the left. The support interval
is [-m,m], including both endpoints; nonzero z is required by the Laurent
shift identities. No spectral conclusion or asymptotic estimate is assumed.

Proof plan: first turn the established support bound into finite support.
Mathlib's finite-support sum permits a bijective integer reindexing without
any convergence obligation. Reindexing k-r multiplies the generating sum
by z^r. The concrete coefficient recurrence and its zeroth coefficient
then give induction on m. Finally replace the finite-support sum by the
displayed finite sum using its proved support inclusion. In particular,
the totalized finite-support-sum operator is never used to hide an infinite
support or a missing convergence hypothesis.

This supplies the actual scalar symbol identity needed by a later
recurrence or circulant bridge. It does not prove Target and earns no
completed-problem count. A local Lean run, independent review, and any
future Comparator run must be recorded separately.
