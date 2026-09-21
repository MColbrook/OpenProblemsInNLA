# Independent zero-endpoint phase review

Verdict: **APPROVE**, for the exact definitions and seven public results
in `PhaseZero.lean`, including the coordinator's real finite-sum proof.
This proves the smooth phase sum and its zero endpoint, not the π
endpoint or the later spectral phase-indexing argument.

Reviewer: `/root/mf21_restart_lean_audit`, 20 September 2026. I did not
author or edit this module. I inspected its complete final source, lock,
unchanged manuscript equations (3), (7), and the factorization following
(8), plus its recorded local execution. I ran no compiler. The pinned
referee standard has SHA-256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Exact sources and execution artifacts

Paths are relative to `MF21-restart`.

| Path | SHA-256 |
| --- | --- |
| `MF21Restart/PhaseZero.lean` | `ac803ba9621d41d11d7ccff77c53299fdf6f13f9caf98e99b6692d4a3cb78885` |
| `PHASE_ZERO_STATEMENTS.md` | `6c98646ed8ffff1db1fd475cd2aa0b305471c22785e069a3cb7f369a9277816c` |
| `MF21Restart/PhaseFactor.lean` | `4b681c97f6c26935ab1a495703f9d648c7fb36c77746d47f9637e6fe741be238` |
| `MF21Restart/RootParameters.lean` | `c784f609c8eeba69db1ec5e7d3ca52ba0611777d662556c8fd8b6321b60af1fa` |
| `original-proof/solution.md` | `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa` |
| `evidence/logs/phase-zero-04.log` | `2aa61ea9aed37468d0de84b5e9c6da7a31d225510404309f84acf5b0c0dacc4a` |
| `evidence/logs/phase-zero-04.json` | `6003095eb5114b618fca9c0a872a58e96d9288046f0a93a696c8ef4696d5c953` |
| `.lake/build/lib/lean/MF21Restart/PhaseZero.olean` | `28309c4ddb8b1e7a1e2e8211566d66d12b2ea77cf8372141bc74bc22aa6382d3` |

The execution record reports an actual local run from
`2026-09-20T20:13:22.718945+00:00` to
`2026-09-20T20:13:30.710280+00:00`, with `LEAN_NUM_THREADS=1` and command

```text
lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/PhaseZero.olean MF21Restart/PhaseZero.lean
```

It records exit code 0, unchanged source, and `comparator: not_run`.
I independently rehashed the source, log, and output artifact; all three
match that record exactly. This is evidence of a local run, not GitHub
Comparator execution.

## Definitions and individual endpoint branches

`PhaseZero.lean:20–25` defines ψ as the finite **sum of individual real
principal arguments**, evaluated through the previously proved smooth
extension. The `Fin(m-1)` index plus one enumerates exactly the published
indices `1,...,m-1`. It defines η as `θ+2*ψ`, as in manuscript (3),
`solution.md:44–52`. There is no substitution of a principal argument
of a product, so the sum is allowed to exceed π.

Lines 28–46 prove the literal identity

`κ_ell+i = 2*sin(π*ell/(2*m))*exp(i*π*ell/(2*m))`.

It is derived from the actual exponential parameter definition, the
π/2 shift, and double-angle identities. The coefficient, factor 2, and
denominator `2*m` match `solution.md:103–107`. All divisions in this
identity are real. The unrestricted statement at `m=0` is valid under
field totalization: κ=-i and both sides are zero. It does not assert a
principal-angle formula in that degenerate case.

Lines 49–71 then impose the real manuscript index conditions
`1<=ell<m`. They derive `m>0` and establish the strict half-angle bounds
`0<alpha<π/2`. Thus the sine prefactor is **strictly positive**, and
the principal argument of `exp(i*alpha)` is exactly alpha. The proof
supplies the required principal-angle range instead of silently
discarding a multiple of 2π. It evaluates `arg(phaseNormalized κ 0)`
using its nonzero value κ+i; it never evaluates the original vanishing
factor at zero via totalized `arg 0`.

## Positive-θ agreement and genuine smoothness

Lines 74–83 identify the sum with precisely the original expression in
(3) when `0<θ<=π`. The previously proved argument equality is used for
each term. The excluded lower endpoint is necessary because the original
factor vanishes there. Its inclusion at θ=π is valid.

Lines 86–94 prove smoothness at every point of `[0,π]` by finite summation
of the actual `individualPhase` functions. Each parameter's positive real
part follows from its verified index range; this is not a new smoothness
or branch assumption. The use of `ContDiffAt` supplies ordinary local
neighborhood smoothness at both endpoints, rather than only a one-sided
claim. Lines 96–99 give the corresponding η theorem by addition and
scalar multiplication. At m=1 the finite sum is empty, so these proofs
and the zero endpoint formulas remain coherent.

## Finite-sum proof and exact endpoint normalization

The private helper at lines 101–110 proves directly over ℝ that
`sum_{ell:Fin N} (ell.val+1) = N*(N+1)/2`. The induction splits the
`N+1`-element finite set into its first N indices and its final index N;
the added term is consequently N+1. No integer division or floor is
present in that formula, and no asserted Gauss-sum value is used as a
premise.

At lines 113–133, `m>=1` justifies both
`((m-1:ℕ):ℝ)=(m:ℝ)-1` and the nonzero denominator m. The helper gives
`sum_{ell=1}^{m-1} ell = m*(m-1)/2` in real arithmetic. Each individual
endpoint contribution is `π*ell/(2*m)`, hence their sum is
`(m-1)*π/4`, with the correct factor 4. Lines 135–138 then give
`η(0)=(m-1)*π/2` by the literal definition η=θ+2ψ.

These are exactly the two zero-endpoint values in manuscript (7),
`solution.md:77–82`. As a simple indexing check, m=1 yields 0, m=3
yields ψ(0)=π/2, and m=6 yields ψ(0)=5π/4. The last value confirms why
the real sum must not be reduced to a single principal argument.

The `m>=1` condition is meaningful for these formulas: at m=0 the empty
sum would be zero while the displayed real expression `(m-1)*π/4`
would be negative. The theorem correctly excludes that invalid case.

## Trust and remaining scope

The successful local log prints all seven public results with exactly
`propext`, `Classical.choice`, and `Quot.sound`. The only warning is an
unnecessary tactic sequencing combinator after `field_simp`. The source
has no `sorry`, `admit`, custom axiom, unsafe shortcut, `native_decide`,
legacy import, or Challenge import. Earlier failed compilation attempts
are not substituted for this source-matched successful execution.

The exact lock matches the source's definitions, hypotheses, and
conclusions. No correctness or fidelity change is requested. Root
conjugation, cancellation of the individual π-endpoint phases,
`ψ(π)=0`, `η(π)=π`, the implicit-phase construction, spectral phase
indexing, determinant estimates, and the complete MF-21 Target remain
outside this module's approved scope. No unrun Comparator check or
additional completed original problem is claimed.
