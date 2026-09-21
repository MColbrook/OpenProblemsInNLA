# Actual Fourier recurrence: statement lock

Statement lock for MF21Restart/FourierRecurrence.lean, 20 September 2026.
The inputs are the concrete coefficient definition and the proved finite
Laurent identity and endpoint coefficient; no array recurrence or spectral
representation is assumed.

First prove, in namespace MF21Restart:

    theorem fourierCoeff_shifted_laurent_sum
        (m : ℕ) (z : ℂ) (hz : z ≠ 0) :
        (∑ t : Fin (2 * m + 1),
          (fourierCoeff m ((t.val : ℤ) - (m : ℤ)) : ℂ) * z ^ t.val) =
          z ^ m * (2 - z - z⁻¹) ^ m

The left exponents are natural powers 0,...,2m. Reindexing the already
proved Laurent sum uses k=t-m and multiplication by z^m. The statement
includes m=0, where both sides are 1. Nonzero z is the natural domain of
the Laurent identity.

Define the specific normalized recurrence:

    def fourierRecurrence (m : ℕ) (lam : ℂ) : LinearRecurrence ℂ where
      order := 2 * m
      coeffs i :=
        ((if i.val = m then lam else 0) -
          (fourierCoeff m ((i.val : ℤ) - (m : ℤ)) : ℂ)) /
          (fourierCoeff m (m : ℤ) : ℂ)

Mathlib's convention is u(n+order)=sum_i coeffs(i)*u(n+i), and its
characteristic polynomial is X^order-sum_i coeffs(i)*X^i. The denominator
here is exactly the outer Fourier coefficient a_(m,m)=(-1)^m, whose
nonvanishing has a separate proof from the actual integral. The central
spectral term has index m; it is not shifted to m-1 or m+1.

Prove the precise characteristic-root implication:

    theorem fourierRecurrence_charPoly_isRoot
        (m : ℕ) (hm : 1 ≤ m) (lam z : ℂ) (hz : z ≠ 0)
        (hvalue : (2 - z - z⁻¹) ^ m = lam) :
        (fourierRecurrence m lam).charPoly.IsRoot z

The hypothesis m>=1 ensures the central index m lies strictly below the
terminal index 2m. It is required here even though the shifted polynomial
identity holds at m=0. The definition is total at m=0, but no spectral
root assertion is made for that degenerate order-zero recurrence.

The proof must split the shifted sum into indices below 2m and its actual
terminal term, use hvalue, and divide only after proving the endpoint
coefficient nonzero. This establishes the concrete recurrence needed to
instantiate RecurrenceBasis. It still does not construct the full list of
roots, prove their distinctness, or identify Toeplitz eigenspaces with
boundary kernels. It makes no asymptotic Target, completed-problem, or
unrun verification claim.
