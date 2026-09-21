# Actual phase product: statement lock

Locked on 20 September 2026 before writing `MF21Restart/PhaseProduct.lean`.
The coordinator approved the names, positive phase sign, and scope below.
Use the unchanged real phase `manuscriptPsi`, which is the **sum of the
individual arguments**, not the principal argument of a product.

Define the literal product f before manuscript (15), with z=exp(i*theta):

```lean
def manuscriptPhaseProduct (m : ℕ) (theta : ℝ) : ℂ :=
  ∏ ell : Fin (m - 1),
    (1 - stableRootCurve (rootKappa m (ell.val + 1)) theta *
      (oscillatoryRoot theta)⁻¹)

def normalizedPhaseProduct (m : ℕ) (theta : ℝ) : ℂ :=
  ∏ ell : Fin (m - 1), phaseNormalized (rootKappa m (ell.val + 1)) theta
```

The natural index ell+1 runs exactly from 1 through m−1. At m=1 the
products are empty and equal one. Definitions are total at m=0 as well.

Prove the normalized product is `ContDiff ℝ ⊤` on the real line for
m>=1, and nonzero at every theta in `[0,pi]`, by the actual factors'
proved regularity and positive real parts. No regularity or nonzero
product assumption may be introduced. Its zero value may be exposed as
the exact finite product of `rootKappa m (ell.val+1) + Complex.I`.

The exact polar identity is valid for all m and all real theta:

```lean
theorem normalizedPhaseProduct_polar (m : ℕ) (theta : ℝ) :
    normalizedPhaseProduct m theta =
      (‖normalizedPhaseProduct m theta‖ : ℂ) *
        Complex.exp ((manuscriptPsi m theta : ℂ) * Complex.I)
```

Derive this by multiplying the polar representations of the **individual**
`phaseNormalized` factors and using the exponential of the real sum of
their individual arguments. The sum can exceed pi. No identity equating
`manuscriptPsi` with the principal argument of the product is asserted
or used. Even if an individual normalized factor vanishes outside the
specified interval, the individual polar representation remains true
because its norm is zero.

The exact factorization is also valid for every m and real theta:

```lean
theorem manuscriptPhaseProduct_factorization (m : ℕ) (theta : ℝ) :
    manuscriptPhaseProduct m theta =
      ((2 * Real.sin (theta / 2) : ℝ) : ℂ) ^ (m - 1) *
        normalizedPhaseProduct m theta
```

This follows from the actual factor identity and
`(oscillatoryRoot theta)⁻¹ = exp(-i*theta)`. It retains exactly m−1
factors of `2*sin(theta/2)`, with no reciprocal or sign change.

On `0<theta<=pi`, the real factor `2*sin(theta/2)` is strictly positive.
For m>=1, prove the three precise conclusions:

```lean
theorem manuscriptPhaseProduct_ne_zero
    (m : ℕ) (hm : 1 ≤ m) (theta : ℝ)
    (htheta : 0 < theta) (htheta_pi : theta ≤ Real.pi) :
    manuscriptPhaseProduct m theta ≠ 0

theorem manuscriptPhaseProduct_polar
    (m : ℕ) (hm : 1 ≤ m) (theta : ℝ)
    (htheta : 0 < theta) (htheta_pi : theta ≤ Real.pi) :
    manuscriptPhaseProduct m theta =
      (‖manuscriptPhaseProduct m theta‖ : ℂ) *
        Complex.exp ((manuscriptPsi m theta : ℂ) * Complex.I)

theorem manuscriptPhaseProduct_div_conj
    (m : ℕ) (hm : 1 ≤ m) (theta : ℝ)
    (htheta : 0 < theta) (htheta_pi : theta ≤ Real.pi) :
    manuscriptPhaseProduct m theta /
        (starRingEnd ℂ) (manuscriptPhaseProduct m theta) =
      Complex.exp (((2 * manuscriptPsi m theta : ℝ) : ℂ) * Complex.I)
```

The final phase sign is **+2*psi**: conjugation negates the phase in
the denominator. Nonvanishing must justify cancellation of the common
norm. The lower endpoint zero is excluded from this ratio statement,
since f itself vanishes there for m>=2; the normalized product still
has a well-defined, nonzero polar representation at zero. The upper
endpoint pi is included. Outside this interval, the scalar factor can
be negative, so the actual product's polar identity is not generalized
without accounting for that sign.

These are the exact product and phase facts used around manuscript
(15)–(16), `original-proof/solution.md:171–189`. They do not yet prove
the two dominant Laplace-coefficient identities, their opposite signs,
the normalizer formula, or any remainder estimate. They do not establish
the MF-21 Target or add a completed original problem. The author runs
no compiler; serialized local tests and any later GitHub Comparator
result must be recorded separately.
