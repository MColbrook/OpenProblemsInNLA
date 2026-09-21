# Independent phase-factor review

Verdict: **APPROVE**, for the exact factorization, normalized factor, and
individual principal-phase extension in `PhaseFactor.lean`. This is a
partial result from manuscript Lemma 2, not its full phase construction.

Reviewer: `/root/mf21_restart_lean_audit`, 20 September 2026. I did not
author or edit the proof file. I independently inspected its original
mathematical argument and statement lock, then supplied suggestions for
elaboration/cast repairs after failed local attempts and inspected the
final repaired source. The definitions and theorem statements did not
change. I ran no compiler. Review follows the pinned referee standard,
SHA-256 `e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Final source and local evidence

Paths are relative to `MF21-restart`.

| Path | SHA-256 |
| --- | --- |
| `MF21Restart/PhaseFactor.lean` | `4b681c97f6c26935ab1a495703f9d648c7fb36c77746d47f9637e6fe741be238` |
| `PHASE_FACTOR_STATEMENTS.md` | `f1c7c9ac193c4800de48fff60f20f72d78db417187340cc5ccb94a1f9ca9285b` |
| `MF21Restart/StableRootSmooth.lean` | `241296dc3b8ac1ca554a1685162f9952d7e4825d170abf56cba8d54f233f4011` |
| `MF21Restart/StableRootAlgebra.lean` | `f1b6459dc1372fba3bb5762c0cb557c4e082443e1be8d09506419bd43d59dde5` |
| `original-proof/solution.md` | `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa` |
| `evidence/logs/phase-factor-04.log` | `d5508a1640847ae59c54d0f0c7c8771f7df9e55303262b4726b53146e225dc37` |

The coordinator reports the actual serial `phase-factor-04` process exited
0. I independently read this log and checked the exact source hashes.
All six public results print exactly `propext`, `Classical.choice`, and
`Quot.sound`; there is no error or `sorryAx`. The two warnings concern
unnecessary tactic sequencing only. Attempts 01–03 failed and are **not**
accepted proof evidence; their error-recovery axiom reports must not be
used as successful verification. Static inspection of the final source
found no `sorry`, `admit`, custom axiom, unsafe shortcut, `native_decide`,
legacy import, or Challenge import.

## Literal factor and endpoint

Write `s=sin(θ/2)`, `c=cos(θ/2)`, `b=sqrt(1+(κ*s)²)` and
`r=(b-κ*s)²`. Lines 13–17 define

`Pκ(θ)=exp(-iθ)*(κ*b+i*c-(1+κ²)*s)`.

The coefficient, sign, and half-angle terms are all necessary. Since
`b²=1+κ²*s²` and `exp(iθ)=1-2*s²+2*i*s*c`, direct subtraction gives
`exp(iθ)-r=2*s*(κ*b+i*c-(1+κ²)*s)`. Lines 21–46 formalize precisely this
identity, obtaining `1-r*exp(-iθ)=2*s*Pκ(θ)` for every κ and θ. No division
by s or cancellation at zero is used, so the identity also holds at θ=0.

Lines 48–49 prove `Pκ(0)=κ+i`. This is the manuscript's limiting
nonvanishing factor in `solution.md:103–107`: the scalar `2*sin(θ/2)`
has first derivative 1 at zero. The module does not expose a separate
derivative-of-that-scalar or quotient-limit theorem, and neither is
counted as an additional formal result here.

For the actual indices, `Re κ>0`; hence `κ+i` is nonzero. The unnormalized
factor itself vanishes at zero. Defining the extended phase as the raw
factor's totalized `arg 0` would therefore be wrong in general. Line 19
instead defines `individualPhase κ θ = arg(Pκ(θ))`, retaining the correct
limiting principal argument.

## Branch, positivity, and smoothness

Lines 52–74 prove global real smoothness of P using the previously proved
slit-plane membership of `1+(κ*sin(θ/2))²` for `Re κ>0`, complex
holomorphic square-root smoothness there, the real sine/cosine maps, and
the exponential. This is the actual principal branch, not an arbitrary
smooth square root. The exact complex-to-real scalar restrictions and
the final explicit function application are proof elaboration steps;
they do not change the mathematical function or smoothness conclusion.

Lines 76–101 prove `Re Pκ(θ)>0` on the full closed interval `[0,π]`.
At zero this follows from `Pκ(0)=κ+i`. For positive θ, the proved stable
root satisfies `|r|<1`, the exponential has modulus 1, and thus
`Re(r*exp(-iθ))<1`. Taking the real part of the exact factorization gives
`1-Re(r*exp(-iθ)) = (2*sin(θ/2))*Re Pκ(θ)` with a strictly positive
real scalar. This proves strict positivity, including θ=π. There is no
unsupported inference from a nonnegative real part at a possible zero.

Lines 103–111 prove equality with the original principal argument only
for `0<θ<=π`. They use the positive-real-scalar identity
`arg((2*sin(θ/2))*P)=arg(P)`; this preserves the principal argument
exactly, without a modulo-2π statement. No positive-real-part condition
on κ is needed for this algebraic argument equality itself. The stricter
condition remains in the smoothness and nonvanishing theorems where it
is mathematically required.

Finally, lines 113–123 use `Re P>0` to place P in the complex logarithm's
slit plane, compose the **local** smooth logarithm with P, and take its
imaginary part. Mathlib's `Complex.log_im` is the identity with the
actual principal argument. The conclusion is `ContDiffAt ℝ ⊤` at every
point of `[0,π]`, including both endpoints, not merely differentiability
from within the interval. Global smoothness of P plus local slit-plane
membership at its value justifies the needed neighborhood at each point.
There is no claim that `individualPhase` is smooth on the whole real line.

## Scope and independent sanity check

This module handles each individual principal argument. It defines no
phase of a product and makes no inference replacing a sum of arguments
by one principal argument. That distinction is essential: for m=6 the
manuscript's limiting sum is `5π/4`, outside the principal argument range.

As a supplementary floating-point check, I evaluated the explicit
formulas for the actual κ indices at m=3,4,6 and θ=0, 10⁻⁵, π/2, π.
The factorization residuals were below `5e-16`, all sampled P values had
positive real part, and the positive-θ roots had norm below 1. Summing
the individual zero-endpoint phases gave respectively `π/2`, `3π/4`,
and `5π/4`; the π-endpoint sums were within `4e-16` of zero. These are
diagnostic branch checks only, not Lean proof premises or formal proofs
of those summed endpoint identities.

Remaining declarations include the exact angle
`arg(κ_ell+i)=π*ell/(2*m)`, conjugation of the actual roots, the finite
sum defining ψ, its endpoint sums, and the resulting η endpoint values.
The module also does not prove the exponential root estimate, derivative
bounds, determinant normalization/error bounds, phase indexing, or the
full MF-21 Target. No GitHub Comparator success or completed original
problem is claimed by this review.
