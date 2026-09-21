# Independent review: high-phase remainder smallness

Verdict: **APPROVE the stated intermediate estimate.** No material statement,
source-fidelity, or proof defect found. This is not a root existence, uniqueness,
counting, or indexing theorem, and it does not complete Lemma 4 or MF-21.

Reviewer: `/root/mf21_restart_lean_audit`, 20 September 2026. The coordinator
authored this module; this reviewer made no source changes and ran no compiler.
Review follows the pinned `REFEREE_STANDARDS.md`, SHA256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Exact sources and execution evidence

All paths are relative to the MF21-restart project. The reviewer independently
computed these hashes and matched the execution record to the current files.

| Artifact | SHA256 |
|---|---|
| `MF21Restart/SpectralWindowBounds.lean` | `4e188878d1a1b079f0569bd010bfa88f7b151ea690453d7efb8500789ca9efd3` |
| `SPECTRAL_WINDOW_BOUNDS_STATEMENTS.md` | `3c6ac1b5f7233f263e62d964eb022464d5056033f5fac770105c6557d61a3945` |
| `evidence/logs/spectral-window-bounds-01.json` | `b2905684de66525c4271e3f56a702c88919b95c98d4b9aeb730744afdbd542c3` |
| `evidence/logs/spectral-window-bounds-01.log` | `9f3e6360135837232ff2d60e717a61268a532df3cc257ff3e36e5a8bff4a94c5` |
| `.lake/build/lib/lean/MF21Restart/SpectralWindowBounds.olean` | `44d822e6cac370ecf3de9a4b3411307c0b6db6ee8e3ca8cb0e41fec8cb25748c` |

The JSON records the actual command `lake env lean -j1 -M4096 -o
.lake/build/lib/lean/MF21Restart/SpectralWindowBounds.olean
MF21Restart/SpectralWindowBounds.lean`, `LEAN_NUM_THREADS=1`, exit_code=0,
and source_unchanged=true. The log has one axiom report, for
`MF21Restart.manuscriptError_high_phase_small`, depending only on `propext`,
`Classical.choice`, and `Quot.sound`. There are no error lines or `sorryAx`.
This is a successful local development test, not a GitHub Comparator run.

The manuscript is `original-proof/solution.md`, SHA256
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`.
The exact matched passage is line 237, after equation (20). The full Lemma 4
statement is at lines 221–226; its subsequent root and counting arguments at
lines 239–257 are outside the present theorem.

## Statement and proof audit

1. `SpectralWindowBounds.lean:30–35` has the intended quantifier order:
   for each m>=2, there is one natural J>=1 which works for every natural n
   and every theta in [0,pi] satisfying `F_n(theta)>=J*pi-pi/4`.
   It proves the literal strict bounds `|E_n|<1/4` and
   `|E_n'|<(n+2)/8`. Neither smallness nor a root is a premise.
   The statement matches the lock at lines 6–19. Covering all n is a sound
   strengthening of the manuscript's sufficiently-large-n scope, as the
   proof below requires no lower bound on n. The high-phase range may be
   empty for small n. It is not a permanently impossible premise: the
   established identity `F_n(pi)=(n+1)*pi` puts pi in this range for n>=J.

2. The functions are the actual previously constructed functions.
   `PhaseMonotonicity.lean:35–36` defines
   `F_n(theta)=(n+2)*theta-eta(theta)`, and its lines 11–33 prove a compact
   bound for the actual eta. That source has SHA256
   `0c0e3034173e4a00103d31eb702356c037f71617ed8e3c4e67f7c69b3b7f7300`.
   `DeterminantRemainder.lean:86–102` defines E as the real part of the
   concrete finite remainder and establishes its ordinary derivative;
   lines 114–127 derive the uniform estimates in (11). Its source has
   SHA256 `3ff379de253810a3edaf355a243e26981c46d0052ca636aac5ace9b82bb6f318`.
   No arbitrary function or assumed decay estimate replaces these objects.

3. Lines 9–26 construct the scalar exponential threshold symbolically:
   `L=max(0,log(8*C)/c)+1`. Since c,C>0, this has L>0 and
   `log(8*C)<c*L`, hence `C*exp(-c*L)<1/8`.
   The logarithm's argument is positive; the division by c is justified.
   The proof does not use interval sampling or a numerical approximation.

4. Lines 36–49 choose c,C,B,L before J and choose J before n or theta.
   The choice `J*pi>L+B+9*pi/4` is correctly large enough because
   `n*theta=F_n(theta)+eta(theta)-2*theta`,
   `eta(theta)>=-B`, and `theta<=pi`. Thus in the required range,
   `n*theta>=J*pi-pi/4-B-2*pi>L`.
   The proof uses the lower bound on eta, with the correct sign, and does
   not accidentally estimate `(n+2)*theta` in place of `n*theta`.

5. Lines 50–65 use c>0 to reverse the inequality in the negative exponent,
   then apply (11). The stronger scalar bound `<1/8` implies the requested
   E bound `<1/4`; multiplying it by the positive `n+1` gives
   `|E_n'|<(n+1)/8<(n+2)/8`. No derivative of the high-phase constraint is
   taken. The proof is valid at pi; theta=0 simply cannot satisfy its
   high-phase constraint for these J. All natural-to-real coercions and
   the threshold `9*pi/4` are consistent with the manuscript formula.

## Trust, scope, and optional polish

A read-only scan of the 47-module project import closure found no `sorry`,
`admit`, custom axiom, unsafe declaration, or `native_decide`, and no import
of `Challenge`. The sole extra import `Numerics` is unused by this new proof;
removing that import would be optional dependency cleanup, not a mathematical
or trust correction. Its existing certificate uses LeanCert kernel mode;
this module performs no new certification or finite enumeration.

This is an independent review of the new threshold proof, the exact imported
statements it uses, and its manuscript correspondence. It is not a second
independent review of this reviewer's own underlying `BoundaryErrorBounds`,
phase-product, or root-construction proofs. No full-target or new-solution
count increases. The module supplies only the high-phase smallness input to
the remaining root-window and indexing argument.

The successful integrated record
`evidence/runs/20260920T213250267591Z/record.json`, SHA256
`799347e39236dd1cee0031b54fd987f7e83e03666e668895715615e3103fc3a2`,
contains 71 earlier module runs and 236 permitted-axiom reports but does not
include this module. The SpectralWindowBounds execution evidence is the
separate actual 01 record above. Comparator remains not run.
