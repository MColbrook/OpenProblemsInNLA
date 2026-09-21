# MF21 PhaseWindowRoots memory-reduction candidate

Status: source-only candidate, **not compiled by this agent**. The root agent owns the sole local Lean compiler slot. No GitHub, Lake, Lean, or Comparator invocation was made by this agent.

## Exact artifacts

| Artifact | SHA256 |
|---|---|
| Original canonical `MF21Restart/PhaseWindowRoots.lean` | `7ababccde85698a360037679ab6d314ca6582f97a0cc09a3a320a38deb7a4590` |
| `/private/tmp/MF21PhaseWindowRootsCandidate.lean` | `7992ba76a6919b9e38aa3758ff74205befe02238e515b66b96584c1848a8d5c8` |
| Unedited `original-proof/solution.md` | `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa` |
| Inspected `/private/tmp/mf21-verifier-tools/linux-second-failed.log` | `4af5ebea1ad9bb2fdfac68f87685135116e21123cd8b235f0d810c6cdd28f04e` |

## Diagnosis and scope

GitHub run 35550709155's supplied log, lines 1303-1309, identifies `MF21Restart.PhaseWindowRoots` as the sole failed required Lake target. Its displayed invocation used Lean 4.33.1, `-j1 -M4096`, and `-o`, `-i`, `-c`, `--setup`, and `--json`; the module failed after 31 seconds with an uncaught `lean::memory_exception` at `interpreter`, exit 134. The log does **not** identify a declaration, tactic, or allocation profile. Unrestricted arithmetic-context processing is a plausible optimization target, not an established diagnosis of the failure.

The pinned local Mathlib source `Mathlib/Tactic/Linarith/Frontend.lean`, lines 341-347, 380-385, and 433-440, confirms that `linarith` includes appropriate local-context comparisons whereas `linarith only [...]` restricts the supplied hypotheses (plus the goal). The original file contains twelve unrestricted invocations, several late in the long scalar-calculus proof. The candidate replaces exactly those invocations with restricted searches over sufficient already-established inequalities. The existing `nlinarith only` at line 211 is unchanged.

## Changes, with static mathematical justification

Line numbers are unchanged between the two sources.

| Line | Exact inputs now used | Why sufficient |
|---|---|---|
| 20 | `Real.pi_pos` | Proves `pi/4 <= pi`. |
| 63 | `hmain`, `(abs_lt.mp hsE).1` | The main derivative is greater than `A/8`; the signed error derivative is greater than `-A/8`; their sum is positive. |
| 90 | `Real.pi_pos` | The two phase levels differ by `pi/2 > 0`. |
| 111, first call | `hl` | Rearranges `k*pi-pi/4 <= F(theta)` into the lower absolute-value inequality. |
| 111, second call | `hu` | Rearranges `F(theta) <= k*pi+pi/4` into the upper absolute-value inequality. |
| 117 | `(abs_le.mp hc).1` | Rearranges the phase-cell lower bound into the lower phase-level comparison. |
| 120 | `(abs_le.mp hc).2` | Rearranges the phase-cell upper bound into the upper phase-level comparison. |
| 146 | `phase_window_margin`, `(abs_lt.mp hEa).2` | `sin(pi/4)>1/4` and signed error `<1/4` make the lower endpoint residual negative. |
| 152 | `phase_window_margin`, `(abs_lt.mp hEb).1` | `sin(pi/4)>1/4` and signed error `>-1/4` make the upper endpoint residual positive. |
| 205 | `hmr` | `2 <= m` implies `0 <= m-1`. |
| 207 | `hzero`, `hkpi`, `Real.pi_pos` | `F(0)<=0`, `pi<=k*pi`, and `pi>0` imply the strict lower endpoint inequality. |
| 218 | `hJkpi`, `(abs_le.mp hc).1` | `J*pi<=k*pi` and `F(theta)>=k*pi-pi/4` imply `F(theta)>=J*pi-pi/4`. |

## Preserved and unverified

Byte-level diff inspection and a Python assertion check establish that the sources have the same number of lines and differ on exactly eleven lines, each containing one of the twelve `linarith` calls listed above. All theorem signatures, hypotheses, definitions, imports, comments, numerical constants, and the mathematical argument are unchanged. No canonical project file, configuration, manuscript, trust declaration, or axiom was edited. No `sorry`, `admit`, native evaluation, additional hypothesis, or resource-limit increase was introduced.

This is the candidate author's static review only, not independent review. Candidate elaboration, its axiom report, resource consumption, final Linux Lake build, and Comparator/kernel/sandbox results remain to be checked by the coordinating agent and independent reviewer. No memory improvement or successful proof check is claimed yet.
