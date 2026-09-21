# Independent root and upper-endpoint component review

Verdict: **APPROVE** for the twelve printed results in `RootDistinctness`,
`StableRootSymmetry`, `StableRootBounds`, and `PhasePi`, at the frozen
source hashes below. I found no material mathematical, statement-fidelity,
or hypothesis-strengthening issue. These are concrete ingredients of
manuscript Lemma 2 and its root list; they are not a completed MF-21
target, determinant remainder estimate, or root-indexing theorem.

I read each actual source and its statement lock independently and
checked the relevant library APIs. I also checked the imported actual
root and phase definitions and the slit-plane argument. This review
does not count as independent review of `RootParameters`,
`StableRootDecay`, or `PhaseZero`, which I authored; those are explicitly
identified dependencies. No reviewed source was edited and no compiler
was run by this reviewer. The pinned referee rubric has SHA256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Exponential parameter identities

`RootDistinctness.rootOmega_pow` (lines 16–27) proves the actual
exponential parameter is an m-th root of unity. The positive m premise
justifies canceling its cast in the exponent; ell is unrestricted, as
it should be. `rootOmega_injective` (lines 29–56) puts the exact real
angles for `Fin m` in `[0,2π)` and applies the actual circle-exponential
injectivity theorem on a half-open interval. The strict upper endpoint
excludes the periodic duplicate at index m. The case m=0 is handled by
the empty domain, not an invalid division cancellation.

`rootKappa_conj` (lines 58–71) proves that the angle at m−ell is the
negative of the angle at ell. Natural subtraction is cast only after
the bound ell<m has supplied ell≤m, and m is proved nonzero. This gives
the exact conjugation equality, with no unnoticed extra sign or
modulo-2π assertion. For the published indices `1≤ell<m`, the reflection
remains in the same range. The statements match their lock and the
parameters in manuscript (2), (8). This module itself does not prove
distinctness of the stable curves or the complete 2m-root list.

## Principal square-root branch and stable-root distinctness

`StableRootSymmetry.sqrt_conj_of_mem_slitPlane` (lines 16–19) uses
`Complex.conj_cpow` only after deriving that the radicand's argument is
not π from slit-plane membership. This restriction is essential: for
z=−1, the principal square root does not commute with conjugation.
The code does not apply a false global conjugation identity.

The actual radicand is `1+(κ*sin(theta/2))²`. The imported proof handles
sin(theta/2)=0 by obtaining radicand 1; otherwise its intermediate
parameter has nonzero real part. If its imaginary part is zero the
radicand is positive real, and otherwise the radicand has nonzero
imaginary part. Thus it avoids the cut for every real theta when
Re κ>0. `stableRootCurve_conj` (lines 21–27) consequently proves
conjugation of the literal quadratic-formula curve, and its indexed
corollary (lines 29–38) uses the actual κ conjugacy. Both legitimately
include theta=0 and theta=π.

`stableRootCurve_rootKappa_injective` (lines 40–72) uses equality of
the root values to equate `2-r-r⁻¹`, then cancels the proved nonzero
factor `2-2*cos(theta)` and invokes the parameter injectivity. That
factor is proved positive from the positive half-angle sine. No root
distinctness or separation estimate is assumed. The explicit `change`
at lines 45–46 only exposes the lambda application for rewriting.
The domain is `0<theta≤π`: at zero all the stable curves equal 1, so
exclusion is necessary once there are multiple stable roots; at π the
stable roots remain distinct even though the two oscillatory roots
coalesce. Small m with an empty or singleton stable-index type causes
no false claim.

## Genuine uniform decay and logarithmic derivative bounds

`StableRootBounds.stable_roots_uniform_exp_decay` (lines 12–36) obtains
the proved individual decay constant for each of the m−1 actual root
parameters and takes their finite minimum. The m≥2 premise makes that
finite set nonempty and covers the manuscript's m≥3 domain. The minimum
is strictly positive, is independent of ell and theta, and is no larger
than the constant for any particular root. Since theta≥0, the exponent
inequality is `-cs_i*theta ≤ -c*theta`, which yields the required upper
bound by monotonicity of exp. Both interval endpoints are included.
The index conversion ell↦ell−1 is guarded by `1≤ell<m`. No uniform
estimate is inserted as a premise.

`stableRootCurve_logarithmic_derivative_bounded` (lines 38–49) concerns
the actual real derivative of the complex-valued curve. Its continuity
comes from the proved smoothness; the denominator is nonzero everywhere
by the actual root theorem. Division therefore gives a continuous
function, whose norm is bounded on the compact interval. Replacing the
bound by `max C 1` ensures the explicitly required strict positivity.
This is a fixed-κ bound as locked. If a later API requires one common
logarithmic-derivative bound over all ell, a further finite maximum is
still needed; that straightforward dependency is not a false proof step
or a missing premise in this result. No logarithm branch or numerical
certificate is used.

## Phase at π is a sum of individual arguments

`PhasePi.individualPhase_pi` (lines 13–16) starts from the proved
equality with the original argument at positive theta and substitutes
`exp(-iπ)=-1`, giving `arg(1+rκ(π))`. It is correctly valid for every κ
because this identity alone needs no modulus hypothesis.
`one_add_stableRootCurve_pi_re_pos` (lines 18–24) then uses the actual
strict norm bound under Re κ>0 to prove the factor has positive real
part. It follows that its principal argument is not π, exactly the
exceptional case in Mathlib's `arg_conj` formula.

`individualPhase_rootKappa_pi_reflect` (lines 26–37) applies the proved
stable-root conjugation at the reflected index and obtains the negative
of the individual argument, with the branch exception excluded above.
`manuscriptPsi_pi` (lines 39–62) uses the exact permutation
`Fin.revPerm` on the m−1 indices. Its value transformation
`ell.rev.val+1 = m-(ell.val+1)` is proved with the index bounds. The
permuted sum equals both the original sum and its negative, so it is
zero. For even m the reflected middle index is fixed and its individual
argument is thereby zero. For m=1 the sum is empty. The final eta
identity (lines 64–66) follows from the actual definition
`eta(theta)=theta+2*psi(theta)`.

This proves precisely the upper endpoint values in manuscript (7).
No step replaces psi by the principal argument of a product. That
distinction is substantive: at m=6 the zero-endpoint sum in the
manuscript is 5π/4, whereas the principal argument of the corresponding
product would be −3π/4. The present endpoint pairing operates on the
individual arguments and has no such wrapping error.

## Scope, trust, and observed local results

The four theorem sets match their respective statement locks. They
assume neither their conclusions nor hidden determinant estimates.
No custom axiom, placeholder, unsafe shortcut, `native_decide`, or
numerical interval computation appears. The small linter warnings in
the root-distinctness and root-bounds logs concern unused tactics or
proof-local instance style and are optional cleanup only.

The coordinator reported actual local exits 0 for RootDistinctness02,
StableRootSymmetry02, StableRootBounds01, and PhasePi01. I read the
corresponding logs: respectively 3, 3, 2, and 4 declarations print only
`[propext, Classical.choice, Quot.sound]`. The observed Symmetry02 and
Bounds01 JSON records also match the current source/log hashes, record
unchanged sources and exit 0, and give the exact `lake env lean -j1
-M4096 -o ...` commands under `LEAN_NUM_THREADS=1`. RootDistinctness02
and PhasePi01 exit-status attribution here comes from the coordinator;
their logs and reviewed source hashes are pinned below. No independent
compiler execution is claimed. No Comparator or GitHub workflow was
run for this review, and the observed JSON records state
`comparator: not_run`.

The full characteristic list, determinant normalization and derivative
estimates, phase-root counting, implicit coefficient construction, and
remaining spectral/asymptotic arguments are separate obligations. These
approved ingredients do not increase the original-problem completion
count.

## Frozen sources and locks

| File | SHA256 |
|---|---|
| `MF21Restart/RootDistinctness.lean` | `1a97a915d9b4058e84e48a564d4f5abddb24a2a68e54e655ca2f97028edbfce5` |
| `ROOT_DISTINCTNESS_STATEMENTS.md` | `4e29cc2168313ca80e31ea61355b271db00469cdaa1bee166ec4c8b58532a177` |
| `MF21Restart/StableRootSymmetry.lean` | `079597268e849c9fbca2adc00d049fce7dd38138278c685b051f5bc7c05700dd` |
| `STABLE_ROOT_SYMMETRY_STATEMENTS.md` | `abc56870ab9aa5694ee9710c9a480b135409967d41d86e9600ed05d4e1938c9d` |
| `MF21Restart/StableRootBounds.lean` | `de3a7eb721977af0be836dff1f6c68b525db5dccd36f5e6b4a68075633052b31` |
| `STABLE_ROOT_BOUNDS_STATEMENTS.md` | `1f635259b148e3ae81faf5037a2a97602bee69e2c8e46577d724e05cfb82d989` |
| `MF21Restart/PhasePi.lean` | `b0ae70dd2c035f312b4858c0ca1f4573bb242e6eb8693404f1330256b49f3e47` |
| `PHASE_PI_STATEMENTS.md` | `4e24a31febfe69a37b64b686186eed630bc51e2deb83ae9e25d09d49229eae26` |
| `MF21Restart/RootParameters.lean` | `c784f609c8eeba69db1ec5e7d3ca52ba0611777d662556c8fd8b6321b60af1fa` |
| `MF21Restart/StableRootSmooth.lean` | `241296dc3b8ac1ca554a1685162f9952d7e4825d170abf56cba8d54f233f4011` |
| `MF21Restart/StableRootDecay.lean` | `edb5b83593d2d7a8dc43e20ec4c77909a8c49662218342683d5e2f1d89911bb2` |
| `MF21Restart/PhaseFactor.lean` | `4b681c97f6c26935ab1a495703f9d648c7fb36c77746d47f9637e6fe741be238` |
| `MF21Restart/PhaseZero.lean` | `ac803ba9621d41d11d7ccff77c53299fdf6f13f9caf98e99b6692d4a3cb78885` |

## Observed evidence hashes

| File | SHA256 |
|---|---|
| `evidence/logs/root-distinctness-02.log` | `dd0248cbd721d9526778e1114a00e3374102a52134eead6c677cc27b802923a1` |
| `evidence/logs/stable-root-symmetry-02.log` | `eafa0ea7e1ef20e4aee3e471f402a4384dee2e11015a8ef89460a966726d820a` |
| `evidence/logs/stable-root-bounds-01.log` | `3bfce3dacf185336e20af5d569665f7c0e28a6e1d066c5fedc8bea4eceae2508` |
| `evidence/logs/phase-pi-01.log` | `b87b51b6e0f2cb8ac85fb1bd227fd06246795472510f973b0463a4a63b797056` |
| `evidence/logs/stable-root-symmetry-02.json` | `2e6dca754081695e1e623bcef27da53eee1275c079c0f619fca496af356991e1` |
| `evidence/logs/stable-root-bounds-01.json` | `45ffe3490bfc10b352fe15f13d1666055bcfe01f1cc07728956eca4c08ff6cdc` |
