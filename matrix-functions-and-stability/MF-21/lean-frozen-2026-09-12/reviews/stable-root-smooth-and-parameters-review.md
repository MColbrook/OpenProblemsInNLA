# Independent smooth-root and parameter review

Verdict: **APPROVE**, for the exact statements of `StableRootSmooth.lean`
and `RootParameters.lean`. These establish part of manuscript Lemma 2,
not the entire lemma or MF-21 Target.

Reviewer: `/root/mf21_restart_lean_audit`, 20 September 2026. I did not
author or edit these modules, and ran no compiler. I inspected their
complete source, statement locks, the actual principal-square-root
dependency, the relevant Mathlib derivative APIs, manuscript (2) and
(8), and the successful local logs. The pinned referee standard is
`/Users/georgestepaniants/Research/project/lean-verification/REFEREE_STANDARDS.md`,
SHA-256 `e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Frozen source and evidence

Paths are relative to `MF21-restart`.

| Path | SHA-256 |
| --- | --- |
| `MF21Restart/StableRootSmooth.lean` | `241296dc3b8ac1ca554a1685162f9952d7e4825d170abf56cba8d54f233f4011` |
| `STABLE_ROOT_SMOOTH_STATEMENTS.md` | `6fb88cf9cff332cb86e0f60be4869f124f597ca98bb9a0d6ce5159c4fabaa22f` |
| `MF21Restart/RootParameters.lean` | `c784f609c8eeba69db1ec5e7d3ca52ba0611777d662556c8fd8b6321b60af1fa` |
| `ROOT_PARAMETER_STATEMENTS.md` | `bd71436b84d079652a403857da654d6a6f2bdf4bb72031561085c65c97973331` |
| `MF21Restart/StableRootAlgebra.lean` | `f1b6459dc1372fba3bb5762c0cb557c4e082443e1be8d09506419bd43d59dde5` |
| `STABLE_ROOT_STATEMENTS.md` | `522987621255dcf06aae486d9904fafe37aca8a3721e37a8effa6aed024ea432` |
| `original-proof/solution.md` | `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa` |
| `evidence/logs/stable-root-smooth-02.log` | `951664caf4c368a43851ae0567003324de7c49f7a56d715356dda7705c6312b9` |
| `evidence/logs/root-parameters-01.log` | `af3dcd223d0360b7d9c7166e431fe2b02c2fb3b05560ca6338c4acfdeeddf57f` |

## Actual branch and smoothness

`StableRootSmooth.lean:15–16` uses the exact previously proved expression
`(sqrt(1+a²)-a)²`, with `a=κ*sin(θ/2)`. The square root is Mathlib's
principal complex square root, defined from complex powers. It is not
an arbitrary root supplied by an existence assumption.

The slit-plane argument at lines 18–42 is sound for every real θ when
`Re κ > 0`. If `sin(θ/2)=0`, the square-root argument equals 1. Otherwise
`Re a != 0`; if `Im a=0`, then `1+a²` has real part `1+(Re a)²>0`, and
if `Im a != 0`, its imaginary part `2*Re a*Im a` is nonzero. Thus the
argument never crosses the negative-real branch cut or zero. The proof
does not incorrectly assume square-root smoothness at an arbitrary
complex point.

Lines 45–60 combine that exact pointwise branch condition with Mathlib's
complex differentiability of the principal square root on the open slit
plane, the holomorphic-to-smooth implication, and restriction of scalars
to ℝ. The sine and polynomial maps are genuinely smooth globally. The
result is `ContDiff ℝ ⊤ (stableRootCurve κ)` on the whole real line,
which supplies an actual neighborhood extension at both 0 and π.
It is stronger than a one-sided interval statement, with a valid proof.

The underlying algebraic module was also read to check branch fidelity.
Its principal square root has strictly positive real part when `Re a>0`;
`(b-a)(b+a)=1` proves nonvanishing and the reciprocal formula. Its norm
argument derives `|b-a|<1`, so the squared branch is inside the unit disk.
There is no assumed inside-root certificate. The separate independent
report `reviews/stable-root-algebra-review.md` applies to the same bytes.

## Derivative, endpoints, and reciprocal equation

`StableRootSmooth.lean:62–72` computes the complex derivative of
`stableQuadraticRoot` at zero as -2. The inner square-root argument has
derivative zero there and value 1, so the principal square-root derivative
API is applied at a regular point. Lines 74–86 compute the real-parameter
derivative of `κ*sin(θ/2)` as `κ/2` and compose, giving exactly `-κ`.
The factor 2 and sign match manuscript (8), `solution.md:93–98`.

The derivative at zero is proved for every κ; local regularity around
the square-root argument 1 makes the absence of a positive-real-part
hypothesis legitimate here. The global smoothness theorem retains that
hypothesis. Lines 88–92 separately prove the value 1 at zero and
nonvanishing for every θ. Consequently the strict norm theorem at lines
94–100 is correctly stated only for `0<θ<=π`; it does not falsely assert
`|r(0)|<1`. Positivity of `sin(θ/2)` includes θ=π and excludes θ=0.

Lines 102–106 specialize the actual reciprocal identity to
`2-r-r⁻¹ = -4*κ²*sin(θ/2)²`. It is an algebraic identity for all κ and θ,
not a criterion assumed to connect a different constructed function to
the manuscript.

The exact value and derivative plus smoothness justify the manuscript's
first-order expansion mathematically. This module does not yet expose
the explicit Lean `O(θ²)` Taylor remainder statement, and that statement
must not be reported as one of its existing declarations.

## Exact root parameters

`RootParameters.lean:16–21` defines the exact complex exponentials
`ω_ell=exp(2πi*ell/m)` and `κ_ell=exp(i*(π*ell/m-π/2))` from real angles.
The divisions are in ℝ, with explicit natural-to-real and real-to-complex
casts. There is no integer-division truncation.

Lines 24–33 prove `Re κ_ell > 0` from exactly `1<=ell<m`. These premises
imply `m>0`; they place `π*ell/m` strictly between 0 and π. The real part
of the exponential is `cos(π*ell/m-π/2)=sin(π*ell/m)>0`. Excluding both
ell=0 and ell=m matters: those would give real part zero and cannot be
used in the global branch argument above. The premises are satisfiable
for all manuscript indices when `m>=3`.

Lines 35–40 prove norm 1 and nonvanishing directly from the exponential.
Lines 43–56 prove `κ_ell²=-ω_ell` using the exact doubled angle and the
exponential's π shift. Neither a sign convention nor that square identity
is taken as a parameter hypothesis. These statements legitimately hold
even for totalized `m=0` definitions: real division by zero then gives
κ=-i and ω=1, so the square identity is still true. Strict positivity is
never asserted there under satisfiable index hypotheses.

Finally, lines 59–73 combine the proved reciprocal equation, this square
identity, and `4*sin²(θ/2)=2-2*cos θ`, giving exactly manuscript (2),
`solution.md:34–41`. The signs multiply to the required positive ω
coefficient. With the actual index and θ hypotheses, this same explicit
curve has norm less than 1 by the earlier theorem, matching the stable
branch chosen by the manuscript.

## Scope still remaining

Neither module assumes or claims a full resolution of Lemma 2. In
particular, the following are outside the proved declarations:

- the finite uniform constant `c>0` in `|r_ell(θ)|<=exp(-c*θ)` and the
  compact-interval bounds on logarithmic derivatives;
- the explicit root-of-unity power identity, uniqueness of the inside
  root, root-list distinctness, and conjugation identities;
- the smooth individual phase, its explicit endpoint angle, the summed
  phases ψ and η, and their endpoint values;
- the determinant error estimates, phase indexing, eigenvalue expansion,
  inverse-kernel theorem, and complete MF-21 Target.

PhaseFactor is a separate reviewed module; its scope and final local
evidence are recorded separately rather than inferred from these two
successful logs.

## Trust and execution

The coordinator reports actual serial local exit code 0 for
`stable-root-smooth-02` and `root-parameters-01`. I independently read
their logs and verified the current source hashes. The former prints
four public axiom reports, the latter five; every report contains exactly
`propext`, `Classical.choice`, and `Quot.sound`. The smoothness log contains
only sequencing-style linter warnings, with no error or `sorryAx`.
Static inspection found no `sorry`, `admit`, custom axiom, unsafe shortcut,
`native_decide`, or legacy/Challenge import in these sources.

This review ran no Lean process and does not certify an unrun GitHub
Comparator check. These partial analytic results do not increase a count
of completed original targets.
