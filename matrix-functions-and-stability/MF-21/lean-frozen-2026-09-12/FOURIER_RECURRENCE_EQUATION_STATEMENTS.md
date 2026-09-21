# Pointwise Fourier recurrence equation

Statement lock for MF21Restart/FourierRecurrenceEquation.lean,
20 September 2026. Import the already proved FourierRecurrence module;
do not redefine its coefficient convention.

Prove exactly, in namespace MF21Restart:

    theorem fourierRecurrence_equation_iff
        (m : ℕ) (hm : 1 ≤ m) (lam : ℂ) (u : ℕ → ℂ) (k : ℕ) :
        (u (k + 2 * m) =
          ∑ i : Fin (2 * m),
            (fourierRecurrence m lam).coeffs i * u (k + i.val)) ↔
        (∑ t : Fin (2 * m + 1),
          (fourierCoeff m ((t.val : ℤ) - (m : ℤ)) : ℂ) * u (k + t.val)) =
          lam * u (k + m)

The theorem quantifies over an arbitrary complex sequence and each
natural starting index. It assumes neither equation, a characteristic
root, nor a representation of the sequence. The left side uses the
order-2m normalized recurrence as defined; the right side includes every
shifted Fourier index -m,...,m and centers the spectral term at k+m.

The proof must split off the terminal t=2m term, evaluate the singleton
central term t=m, and use the already proved nonvanishing of the actual
endpoint coefficient. The condition m>=1 places m strictly before 2m.
Both implications are required; no one-way replacement suffices for the
later finite eigenvector/kernel correspondence.

This is the exact algebraic bridge between the two pointwise equations.
It does not assert zero ghost values, a Toeplitz convolution identity,
root distinctness, boundary-kernel equivalence, or any asymptotic Target.
The coordinator will provide serial local compilation; no compiler or
Comparator result is asserted by this statement lock.
