# Independent review: exclusion below the artificial endpoint root

Verdict: **APPROVE** both stated final-window results. The proof obtains
the required factor pi-theta in the sine lower bound and compares it to
the actual endpoint error estimate. It correctly excludes theta=pi from
the nonvanishing conclusion. No material defect found.

Reviewer: `/root/mf21_restart_lean_audit`, 20 September 2026. The reviewer
did not author or edit this source and ran no compiler. The pinned
referee standards have SHA256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Exact source and actual local run

| Artifact | SHA256 |
|---|---|
| `MF21Restart/FinalPhaseWindow.lean` | `81501dac643fe4505569c895f84d2af10160b35c023ec5b5ab577dd3ee80dc96` |
| `FINAL_PHASE_WINDOW_STATEMENTS.md` | `3c657845c34d77a98d83d46231189c539c202f036061370090b6cb5a9a8a5484` |
| `evidence/logs/final-phase-window-01.json` | `d88978232f1351c4806cd45f040d32881620ff5ad6edc53e61fdf5c5d9099c1a` |
| `evidence/logs/final-phase-window-01.log` | `01774a51667a91a7131992693d7d0b05611b0bba2635b689a9d7abb5831f5eb0` |
| `.lake/build/lib/lean/MF21Restart/FinalPhaseWindow.olean` | `1297fce6de12ff3df46d57ff18bad8357720236be3cdf53c6cb3fec718d4ff26` |

These hashes were independently recomputed, and all three source/log/output
hashes match the actual 01 record. It gives exit_code=0,
source_unchanged=true, `LEAN_NUM_THREADS=1`, and
`lake env lean -j1 -M4096 -o
.lake/build/lib/lean/MF21Restart/FinalPhaseWindow.olean
MF21Restart/FinalPhaseWindow.lean`. Both axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`. No error or `sorryAx`
occurs. This is local development evidence, not a Comparator result.

The exact manuscript passage is `original-proof/solution.md:241–247`,
SHA256 `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`.
The statement lock and code agree on both quantifier orders and domains.

## Findings

1. **The geometric prerequisite uses the actual phase.** Lines 19–41
   choose N from the proved compact bound |eta|<=B, before introducing
   n or theta. On the final closed phase window the lower phase bound
   gives `(n+2)*theta-eta >= (n+1)*pi-pi/4`. If theta<pi/2, the bound
   eta>=-B contradicts the selected `n*pi>2*B+pi`.
   This proves theta>=pi/2 uniformly, including theta=pi. The choice is
   more than large enough and does not incorrectly use the upper bound
   on eta where the lower one is required.

2. **The scalar exponential threshold is proved.** Lines 43–61 derive
   the limit of `exp(-c*n*pi/2)` from c>0 and the standard exponential
   limit at minus infinity. Multiplication by fixed C gives eventual
   `C*exp(-c*n*pi/2)<1/pi`. The result covers every natural n above one
   threshold, not a selected subsequence. No floating-point bound or
   hypothesis of eventual smallness supplies this fact.

3. **The sine bound has exactly the endpoint distance factor.** Lines
   65–104 use the actual phase derivative lower bound and the mean value
   inequality on the convex interval to prove
   `((n+2)/2)*(pi-theta)<=F_n(pi)-F_n(theta)`.
   The endpoint identity is `F_n(pi)=(n+1)*pi`. Jordan's inequality on
   the phase offset, whose absolute value is at most pi/4 and hence
   at most pi/2, yields
   `((n+2)/pi)*(pi-theta)<=|sin(F_n(theta))|`.
   The shift by the natural integer n+1 is removed only inside absolute
   value; its parity sign is therefore harmless and is explicitly
   accounted for. All factors multiplied into inequalities are
   nonnegative. At theta=pi this lower bound is correctly zero.

4. **The final comparison is strict only in the interior.** Lines
   106–140 combine the three actual thresholds by a maximum, still
   depending only on m. The error bound used is the established
   endpoint estimate `C*(n+1)*(pi-theta)*exp(-c*n*pi/2)`, not merely
   a uniform exponential estimate lacking the distance factor.
   Since theta<pi, `(n+1)*(pi-theta)>0`, so eventual exponential
   smallness gives the strict error bound below
   `((n+2)/pi)*(pi-theta)`. This works for angles arbitrarily close
   to pi and for the lower phase endpoint of the closed window.
   There is no invalid cancellation or division at theta=pi.

5. **Actual residual nonvanishing follows without a spectral premise.**
   Lines 141–148 contradict a residual zero using
   `sin(F_n(theta))=-E_n(theta)` and the strict inequality
   `|E_n(theta)|<|sin(F_n(theta))|`. The public conclusion concerns
   the literal `manuscriptResidual`, with no independent error,
   monotonicity, derivative or spectral assumption. The open theta
   interval intentionally leaves the already established artificial
   zero at pi intact. This supports the manuscript's final-cell
   exclusion once combined with the existing eigenvalue criterion.

The imported actual phase estimates in `PhaseMonotonicity.lean` remain at
SHA256 `0c0e3034173e4a00103d31eb702356c037f71617ed8e3c4e67f7c69b3b7f7300`.
The actual endpoint estimate at `DeterminantRemainder.lean:141–174` remains
at SHA256 `3ff379de253810a3edaf355a243e26981c46d0052ca636aac5ace9b82bb6f318`.
The residual definition at `ActualSimpleRoots.lean:22–23` remains at
SHA256 `fd2b696d326d7672d791d41c1368a2b8cfd0a2c8fc1737f32c36a591bd95f6f8`.

## Trust and scope

A read-only scan of the project import closure found no `sorry`, `admit`,
custom axiom, unsafe declaration, `native_decide`, or `Challenge` import.
The new source introduces no numerical certificate or computation grid;
the sine bound is symbolic and uses an existing Mathlib inequality.
All private helper assumptions are discharged by actual theorems in the
public result.

This independent review covers the new final-window argument and its
use of imported interfaces, not this reviewer's own transitive root,
phase-product, or error-bound proof internals. It does not establish
gap exclusion between ordinary windows, the top-down eigenvalue count,
identification of phase label k with sorted index k, the quantitative
angle approximation, or the full MF-21 Target. No original-target count
increases, and no GitHub Comparator/kernel/sandbox check is claimed.
