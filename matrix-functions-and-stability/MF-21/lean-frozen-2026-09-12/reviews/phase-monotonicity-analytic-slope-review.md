# Independent review: actual phase monotonicity and analytic division

Verdict: **APPROVE** for the six printed results in `PhaseMonotonicity.lean`
and the two in `AnalyticSlope.lean`, at the exact hashes below. I found no
material correctness, source-fidelity, or hypothesis issue. The first module
proves manuscript (20) for the actual phase. The second is the analytic
division ingredient for the endpoint factors near (18). Neither proves the
normalized determinant remainder, phase-root indexing, or the MF-21 target.

I independently read both actual sources, their locks, the relevant frozen
manuscript equations, and the Mathlib APIs used for analytic Taylor division,
`dslope`, compact bounds, and the derivative monotonicity theorem. I did not
edit either source or run a compiler. The pinned referee rubric has SHA256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.
`PhaseZero`, which I authored, is a declared dependency rather than a new
independent approval in this report.

## Phase bounds are derived from the actual function

`manuscriptEta_bounded_with_derivative` (lines 11–33) uses the existing
`manuscriptEta_contDiffAt` at each point of `[0,π]`. It derives continuity of
eta and of its actual derivative by evaluating the continuous Fréchet
derivative at 1. The imported smoothness is at the point in the real line,
including the two endpoints; there is no conflation of an unrestricted
derivative with an endpoint `derivWithin`.

Compactness bounds each of the two actual functions, and
`max (max C₁ C₂) 1` gives one strictly positive bound independent of theta.
The bound is obtained in the proof, not assumed in the statement. The
quantifier order permits dependence on the fixed m and excludes dependence
on n. This is exactly the kind of fixed-m bound used in manuscript Lemma 4.

`manuscriptPhaseFn` (lines 35–36) is `(n+2)*theta-eta(theta)`, preserving
the manuscript mesh normalization. Its endpoint theorems (lines 38–45)
use the proved eta endpoints and give
`F_n(0)=-(m-1)*π/2`, `F_n(π)=(n+1)*π`, with the subtraction in the first
value taking place in ℝ. The m≥1 premise matches the existing endpoint
API and includes the whole manuscript domain. The phase dependency is the
sum of individual principal arguments; no argument-of-product replacement
or modulo-2π equality enters this module.

`manuscriptPhaseFn_hasDerivAt` (lines 47–53) derives the ordinary real
derivative `n+2-eta'(theta)` from the actual smooth eta. The derivative
estimate (lines 55–66) chooses `N=Nat.ceil(2*C)` and proves that n≥N
implies n≥2C as an inequality in ℝ. From `-C≤eta'≤C` this gives both
`(n+2)/2≤F_n'` and `F_n'≤2*(n+2)` on the entire closed interval.
The directions and constants agree with manuscript (20); no n+1/n+2 shift
has occurred. The threshold is sufficient without any numerical search.

`manuscriptPhaseFn_eventual_strictMonoOn` (lines 68–80) invokes the library
mean-value consequence on the convex closed interval, supplies continuity
there, and uses the positive derivative lower bound on its interior.
Since n≥0, `(n+2)/2>0`; hence strict monotonicity follows for the same
threshold. It does not assume invertibility or monotonicity of the phase.
At m=1 the empty stable-root sum gives eta(theta)=theta and the expected
linear phase; no endpoint or small-index contradiction is hidden.

This establishes all of (20), but not the subsequent `I_(n,k)` root
existence/counting, a bound on E_n, a simple determinant root, or agreement
of k with the sorted eigenvalue index. Those are explicitly outside the lock.

## The divided analytic function is the genuine dslope

`analyticAt_dslope_zero` (lines 12–31) assumes only that the actual
`f : ℝ→ℂ` is real analytic at zero. Mathlib's
`AnalyticAt.exists_eq_sum_add_pow_mul` at order one supplies an F analytic
at zero with `f(z)=f(0)+z•F(z)` for every z. I inspected this library
theorem: its global equality is obtained by defining the quotient outside
the local analytic neighborhood. It does not infer global analyticity
from a local hypothesis, and the present proof does not make that inference.

Differentiating the displayed factorization at zero proves `f'(0)=F(0)`.
At nonzero z, cancellation proves
`(f(z)-f(0))/z=F(z)`. These two statements identify F with the existing
`dslope f 0`, whose value at zero is the actual derivative. Thus the
analyticity conclusion is about the specific divided function, not an
arbitrary chosen extension with an unproved removable value. It needs
neither f(0)=0 nor f'(0)≠0: subtracting f(0) is part of `dslope`, and the
zero or higher-order cases remain valid.

`analyticAt_dslope_of_forall_analyticAt` (lines 33–43) uses that result at
zero. At a nonzero point it proves analyticity of
`z⁻¹•(f(z)-f(0))` by the library inverse, subtraction, and scalar-action
rules, then uses local equality of `dslope` and `slope`. Its explicit
everywhere-analytic premise is appropriate to its everywhere-analytic
conclusion. The local zero theorem remains available when only a local
root-factor argument is needed, so the endpoint application is not forced
to assume a gratuitous global regularity condition.

I searched the pinned Mathlib analytic/calculus sources for an existing
analytic-dslope result and found no direct duplicate. The proof reuses the
existing order-one analytic Taylor theorem and existing divided-slope
definition rather than introducing a new power-series or quotient API.
It does not prove nonvanishing of a divided root difference: that still
requires the actual distinct first derivatives or other factor-specific
information. It likewise supplies no ratio bound or determinant estimate.

## Trust, evidence, and remaining scope

Both theorem sets match their locks. No custom axiom, placeholder, unsafe
shortcut, `native_decide`, or numerical certificate occurs. The linter
warnings in the observed logs concern an unused simp argument and tactic
sequencing, not a correctness issue. There is no unnecessary numerical
certification or enumeration.

The coordinator reported actual local successful tests for
PhaseMonotonicity02 and AnalyticSlope01; the latter was a direct local
session numbered 86470 with observed exit 0. I read both retained logs,
which print respectively six and two axiom sets, all exactly
`[propext, Classical.choice, Quot.sound]`. This report attributes execution
and success to the coordinator and records the independently inspected
source/log hashes below. No per-test JSON is claimed for these direct
tests, and I performed no local compiler execution, GitHub workflow, or
Comparator check. A future integrated source-matched run remains distinct
from this review.

| File | SHA256 |
|---|---|
| `MF21Restart/PhaseMonotonicity.lean` | `0c0e3034173e4a00103d31eb702356c037f71617ed8e3c4e67f7c69b3b7f7300` |
| `PHASE_MONOTONICITY_STATEMENTS.md` | `325313b093bff3aaa70588b4b88b800b7f37d9896e9573a4170614d23a3dc506` |
| `MF21Restart/AnalyticSlope.lean` | `134bef6e7863c9e9932fde4c220d31a2d019d48a5820bf72e398dc058a2a2dc7` |
| `ANALYTIC_SLOPE_STATEMENTS.md` | `e6c79bdbefb3f5dfd290ef3345c247cbfeb1107ad8f10e8ca1ca98bf7102bcca` |
| `MF21Restart/PhasePi.lean` | `b0ae70dd2c035f312b4858c0ca1f4573bb242e6eb8693404f1330256b49f3e47` |
| `MF21Restart/PhaseZero.lean` | `ac803ba9621d41d11d7ccff77c53299fdf6f13f9caf98e99b6692d4a3cb78885` |
| `MF21Restart/PhaseFactor.lean` | `4b681c97f6c26935ab1a495703f9d648c7fb36c77746d47f9637e6fe741be238` |
| `evidence/logs/phase-monotonicity-02.log` | `dcb4b393b5a6314157c11eccaf2e361427a4a7417fa0b220ab01ce97dde7a1b0` |
| `evidence/logs/analytic-slope-01.log` | `6b1fd6fd790e3d7ca6204c8b7be1bd00051a834cb10c17642ce537aaabe8903d` |
