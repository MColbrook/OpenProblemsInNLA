# Statement lock: actual Fourier coefficients as the binomial stencil

Locked before writing `MF21Restart/FourierBinomialStencil.lean` on
20 September 2026. The original integral definition `fourierCoeff`, the
symbol, and `toeplitz` remain unchanged.

Define the finite complex polynomial, using the actual coefficient:

```lean
def fourierStencilPolynomial (m : ℕ) : Polynomial ℂ :=
  ∑ t : Fin (2 * m + 1),
    Polynomial.C (fourierCoeff m ((t.val : ℤ) - (m : ℤ)) : ℂ) *
      Polynomial.X ^ t.val
```

Prove exactly:

```lean
theorem fourierStencilPolynomial_eq (m : ℕ) :
    fourierStencilPolynomial m =
      Polynomial.C ((-1 : ℂ) ^ m) * (1 - Polynomial.X) ^ (2 * m)

theorem fourierCoeff_shifted_binomial (m t : ℕ) (ht : t ≤ 2 * m) :
    fourierCoeff m ((t : ℤ) - (m : ℤ)) =
      (-1 : ℝ) ^ (m + t) * ((2 * m).choose t : ℝ)
```

Both theorems include m=0 and both support endpoints. The sign is m+t,
so at m=1 the coefficient list is [-1,2,-1], and the central coefficient
t=m is positive. At t=0 and t=2m it agrees with the previously proved
endpoint value (-1)^m. The argument of the Fourier coefficient is an
integer subtraction, not truncated natural subtraction.

Outside the support, reuse the already proved statement without making
a duplicate wrapper:

```lean
fourierCoeff_support (m : ℕ) (k : ℤ)
  (hk : (m : ℤ) < |k|) : fourierCoeff m k = 0
```

The polynomial identity must come from the actual integral-coefficient
Laurent identity `fourierCoeff_shifted_laurent_sum` in the compiled
`FourierRecurrence.lean`, not an assumed generating formula. For each
nonzero complex z, its right side simplifies exactly as

```
z^m * (2-z-z^(-1))^m
  = (z*(2-z-z^(-1)))^m
  = (-(1-z)^2)^m
  = (-1)^m * (1-z)^(2m).
```

Equality on the infinite set of nonzero complex numbers identifies the
two polynomials, including their values at zero. Extract the coefficient
at t using the finite sum and the standard Mathlib binomial coefficient
formula. One convenient route is `(1-X)^(2m)=(X-1)^(2m)` and the existing
formula for the coefficient of `(X+C r)^n`; the parity identity
`(2m-t) mod 2 = t mod 2` is justified by t<=2m.

No eigenvalue asymptotics, matrix inverse, or kernel convergence theorem
is asserted by this component. It supplies the exact coefficient bridge
needed to apply the separately proved weighted binomial identity to the
actual Toeplitz matrix. That inverse route preserves the known
Duduchava–Roch attribution. No new original-target count is warranted.

No compiler is run by the source author. The coordinator performs local
serial tests using one thread and 4096 MiB, retaining source-matched
evidence; GitHub Comparator remains a separate final check.
