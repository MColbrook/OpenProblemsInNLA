# Sum of individual phases and its zero endpoint: statement first

This lock precedes `MF21Restart/PhaseZero.lean`. It formalizes the
factorization immediately after manuscript (8), the zero endpoint in
(7), and the smooth sum in (3), using the actual `rootKappa` and
`individualPhase` functions. The phase is a sum of individual principal
arguments. It is never replaced by the principal argument of a product.

The exact new definitions are:

```lean
def manuscriptPsi (m : ℕ) (θ : ℝ) : ℝ :=
  ∑ ell : Fin (m - 1),
    individualPhase (rootKappa m (ell.val + 1)) θ

def manuscriptEta (m : ℕ) (θ : ℝ) : ℝ :=
  θ + 2 * manuscriptPsi m θ
```

The finite index `ell.val + 1` enumerates precisely `1,...,m-1` when
`1 ≤ m`. At `m=1` the sum is empty and the endpoint formulas are zero.
All angle divisions below are real divisions, including the denominator
`2 * (m : ℝ)`.

The exact public statements to prove are:

```lean
theorem rootKappa_add_I (m ell : ℕ) :
    rootKappa m ell + Complex.I =
      ((2 * Real.sin (Real.pi * (ell : ℝ) / (2 * (m : ℝ))) : ℝ) : ℂ) *
        Complex.exp
          (((Real.pi * (ell : ℝ) / (2 * (m : ℝ)) : ℝ) : ℂ) * Complex.I)

theorem individualPhase_rootKappa_zero (m ell : ℕ)
    (hell : 1 ≤ ell) (hellm : ell < m) :
    individualPhase (rootKappa m ell) 0 =
      Real.pi * (ell : ℝ) / (2 * (m : ℝ))

theorem manuscriptPsi_eq_original (m : ℕ) (θ : ℝ)
    (hθ : 0 < θ) (hθπ : θ ≤ Real.pi) :
    manuscriptPsi m θ =
      ∑ ell : Fin (m - 1),
        (1 - stableRootCurve (rootKappa m (ell.val + 1)) θ *
          Complex.exp (-(θ : ℂ) * Complex.I)).arg

theorem manuscriptPsi_contDiffAt (m : ℕ) (hm : 1 ≤ m)
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi) :
    ContDiffAt ℝ ⊤ (manuscriptPsi m) θ

theorem manuscriptEta_contDiffAt (m : ℕ) (hm : 1 ≤ m)
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi) :
    ContDiffAt ℝ ⊤ (manuscriptEta m) θ

theorem manuscriptPsi_zero (m : ℕ) (hm : 1 ≤ m) :
    manuscriptPsi m 0 = ((m : ℝ) - 1) * Real.pi / 4

theorem manuscriptEta_zero (m : ℕ) (hm : 1 ≤ m) :
    manuscriptEta m 0 = ((m : ℝ) - 1) * Real.pi / 2
```

The elementary complex identity in the first theorem is valid even at
the totalized `m=0`; no argument branch is claimed there. For the actual
published indices, `α = pi*ell/(2*m)` lies in `(0,pi/2)`. Thus its sine
prefactor is positive, and the principal argument of `exp(iα)` is exactly
`α`. Together with `phaseNormalized_zero` this computes the individual
extended phase at zero. It does not take the argument of the original
vanishing factor at zero.

The smoothness proof is the finite sum of the already proved local
smooth individual phases for parameters with positive real part. The
endpoint sum uses Gauss's finite summation identity, with real casts and
the positive denominator justified. No branch identity, root conjugacy,
pi endpoint, determinant normalization, eigenvalue indexing, or complete
MF-21 assertion is assumed or claimed here.

Validation policy: the author does not run a compiler. The coordinator
records the actual serialized local tests separately from independent
source review and any eventual GitHub Comparator run.
