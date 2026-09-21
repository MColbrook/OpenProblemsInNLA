# Independent review: actual simple roots in high phase windows

Verdict: **APPROVE** the stated uniform phase-window theorem. The public
statement derives existence, uniqueness and a nonzero residual derivative
from the actual functions, with no assumed smallness or root-existence
hypotheses. It stops before gap exclusion, the final artificial endpoint
window, and identification of the ordered eigenvalue index.

Reviewer: `/root/mf21_restart_lean_audit`, 20 September 2026. The reviewer
did not author or edit this module and ran no compiler. Review follows
the pinned referee standards, SHA256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Exact evidence

| Artifact | SHA256 |
|---|---|
| `MF21Restart/PhaseWindowRoots.lean` | `7ababccde85698a360037679ab6d314ca6582f97a0cc09a3a320a38deb7a4590` |
| `PHASE_WINDOW_ROOTS_STATEMENTS.md` | `084728210d3e16a889174e6d61e81158b7b775d6e356cc37d26604c61b818c3f` |
| `evidence/logs/phase-window-roots-02.json` | `6a3cb9d82f0d875c63e99d9085d5cdd7d81a292c0269727b511dbfe5daef72f7` |
| `evidence/logs/phase-window-roots-02.log` | `9e4625708663d3fbe14d1eb67bbf5a59401b8674e06985c006d9bd34189dd1c4` |
| `.lake/build/lib/lean/MF21Restart/PhaseWindowRoots.olean` | `22986de16c167d3abc0cf0369c0f0b3a6b31f7f754b2b9dc50aa50be164b94b5` |

The hashes were independently recomputed and matched to the actual 02
record. It records exit_code=0, source_unchanged=true, `LEAN_NUM_THREADS=1`,
and `lake env lean -j1 -M4096 -o
.lake/build/lib/lean/MF21Restart/PhaseWindowRoots.olean
MF21Restart/PhaseWindowRoots.lean`. Its single axiom report, for
`manuscriptResidual_unique_root_in_phase_windows`, contains only
`propext`, `Classical.choice`, and `Quot.sound`. The warnings are unused
simp/sequence-focus cleanup, not missing proofs. This is local test
evidence only; Comparator is not run.

The unchanged manuscript is `original-proof/solution.md`, SHA256
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`.
The exact covered passage is lines 237–239 of the Lemma 4 proof, through
existence and uniqueness of a simple residual root. Lines 241–257 contain
the separate gap/final-window exclusion, counting and location estimates.

## Statement and mathematical findings

1. **The threshold order is genuinely uniform.** Lines 177–185 quantify
   m first, then choose N,J>=1, then cover every n>=N and J<=k<=n.
   The unique theta is in `(0,pi)` and in the closed phase window
   `|F_n(theta)-k*pi|<=pi/4`, and is a zero of the literal residual.
   The derivative is nonzero at every theta in that whole window, a
   correct strengthening of simplicity at its unique zero. There is no
   index equality `j=k` in the conclusion. The exact type agrees with
   the statement lock and is useful for arbitrarily large n, including
   k=n; it is not made vacuous by a window-size restriction.

2. **Parity is handled with the correct sign.** Lines 26–43 define
   `R=(-1)^k*(sin(F)+E)` and rewrite it as
   `sin(F-k*pi)+(-1)^k*E`. Its derivative is
   `cos(F-k*pi)*F'+(-1)^k*E'`. The error is multiplied by the same parity
   factor as the sine; no sign is dropped for odd windows. Multiplication
   by this nonzero factor preserves zeros and derivative nonvanishing.

3. **The derivative margin is sufficient and strict.** Lines 17–24
   use cosine monotonicity on the absolute phase offset to obtain
   `cos(offset)>=cos(pi/4)>1/4` throughout the closed window. The exact
   equality of sin(pi/4) and cos(pi/4) reuses `phase_window_margin`.
   Lines 45–63 combine `F'>=A/2`, A>0, and `|E'|<A/8` to give
   `cos(offset)*F'>A/8`, hence R'>0. The manuscript's sharper
   `A/(2*sqrt(2))` bound is unnecessary: this weaker proved margin is
   already strict enough, with the same error threshold.

4. **Both window endpoints are constructed, not assumed.** The private
   calculus argument at lines 67–120 derives strict monotonicity of F
   on `[0,pi]` from the lower derivative bound and continuity. IVT gives
   a,b with phase values `k*pi-pi/4` and `k*pi+pi/4`. The strict endpoint
   inequalities imply `0<a<b<pi`. Monotonicity proves both directions
   of the correspondence between `[a,b]` and the phase-window inequality.
   Therefore uniqueness on `[a,b]` applies to every candidate in the
   full stated theta domain, not merely a smaller chosen subinterval.

5. **Existence and uniqueness use exact signs and continuity.** Lines
   121–152 establish R'>0 throughout `[a,b]` and opposite strict endpoint
   signs. The sine at a is `-sin(pi/4)`, at b it is `sin(pi/4)`, and the
   parity-scaled error has absolute value below 1/4. Lines 153–164 apply
   IVT and strict monotonicity to obtain exactly one residual zero.
   Lines 165–173 transfer R'>0 to nonzero derivative of the original
   unscaled residual, including the phase endpoints. No numerical root
   finder, isolated sign sample, or assumed residual zero appears.

6. **The public theorem discharges the private calculus assumptions.**
   Lines 186–222 take N from the actual eventual phase derivative bound,
   J from the actual high-phase error estimate, and replace N by max(N,1).
   The two actual differentiability theorems supply the derivatives.
   `F_n(0)=-(m-1)*pi/2<=0` and k>=1 give the strict lower endpoint
   inequality. `F_n(pi)=(n+1)*pi` and k<=n give the strict upper one,
   even in the top k=n cell. Finally the cell lower bound and k>=J imply
   `F_n(theta)>=J*pi-pi/4`, justifying the actual smallness theorem.
   Thus no abstract estimate remains as a public premise. These are
   ordinary derivatives on the real line, with the previously proved
   regularity at the closed interval's endpoints.

Imported interfaces checked against current files:

| Source | SHA256 |
|---|---|
| `MF21Restart/PhaseMonotonicity.lean` | `0c0e3034173e4a00103d31eb702356c037f71617ed8e3c4e67f7c69b3b7f7300` |
| `MF21Restart/SpectralWindowBounds.lean` | `4e188878d1a1b079f0569bd010bfa88f7b151ea690453d7efb8500789ca9efd3` |
| `MF21Restart/ActualSimpleRoots.lean` | `fd2b696d326d7672d791d41c1368a2b8cfd0a2c8fc1737f32c36a591bd95f6f8` |
| `MF21Restart/Numerics.lean` | `9d8eb86229773759393cecd14b2651dfc6a994c270dc1ee82d3131c1af60bc42` |

## Computation, trust, and limits

There is no new computation certificate. The existing single constant
margin in `Numerics.lean:15–20` is reused in LeanCert kernel mode after
exact trigonometric reduction. The proof introduces no grids or changing
numerical precision. A read-only scan of the 52-module project import
closure found no `sorry`, `admit`, custom axiom, unsafe declaration,
`native_decide`, or `Challenge` import.

The independent scope is the new phase-window argument and its use of
the existing interfaces. This is not an independent review of this
reviewer's own transitive root, phase-product and error-bound proof
internals. The theorem deliberately stops before the remaining portions
of Lemma 4: it does not rule out zeros in gaps or near the final artificial
root at pi, count eigenvalues from above, identify the phase label with
the sorted index, construct Y, or give the quantitative angle estimate.
MF-21 remains incomplete; no original-target count increases.
