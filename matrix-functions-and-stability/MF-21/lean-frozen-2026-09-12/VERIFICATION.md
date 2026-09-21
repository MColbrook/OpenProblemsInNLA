# MF-21 verification evidence

The full canonical theorem and the manuscript's smooth coefficient theorem
passed local Lean checking on 20 September 2026. The source manuscript has
not been changed. GitHub Comparator, its kernel replay and Linux sandbox
verification are separate checks; no such success is asserted by the local
records below.

## Actual local checks

- [TargetProof01](evidence/logs/target-proof-01.json) records exit 0 for
  TargetProof.lean, SHA256
  `189eb2e1ed8ad943d78c982e36203cae995e0c6b731293161cb615c9228edf53`.
  It finished at `2026-09-20T23:57:57.116845+00:00`.
- Its [actual axiom output](evidence/logs/target-proof-01.log) covers
  `implicitPhase_critical_bound_impossible`, `manuscript_smooth_target`, and
  `target_proved`, with only `propext`, `Classical.choice`, and `Quot.sound`.
- [Full root02](evidence/logs/full-root-02.json),
  [Solution01](evidence/logs/full-solution-01.json),
  [Challenge01](evidence/logs/full-challenge-01.json), and
  [Audit01](evidence/logs/full-audit-01.json) subsequently compiled the
  combined modules and seven exact contracts. All 386 expected
  [axiom reports](evidence/logs/full-audit-01.log) matched Audit.lean and
  used only the permitted standard axioms.

Every record identifies the real command, successful exit, unchanged source,
source hash, output hash and log hash. All local compiler processes were
serialized with `LEAN_NUM_THREADS=1`, `-j1`, and `-M4096`.
The complete [125-source integration run](evidence/runs/20260921T000301098707Z/record.json)
passed from `2026-09-21T00:03:01.098707+00:00` to
`2026-09-21T00:18:29.089795+00:00`, with all 386 expected axiom reports.
Its record SHA256 is
`abdf520ffbcfc2fe80236e0c303795d97a50e8c11f46a5edbac8a29dba5d7856`.
Every source, dependency pin, log and compiled-output hash was checked again
against that record with no mismatch. The earlier 112-module record predates
final assembly and is retained only as history.

The exact runner used for that successful run is archived beside its record.
The distributed `verify_local.py` subsequently received only a portable
compiler-lock directory selection. The macOS lock location and all compiler
commands are unchanged. Its [Python-only portability check](evidence/runner-portability-smoke.json)
tests path selection, real process exclusion and the unchanged runner body;
it is neither another Lean compilation nor a Comparator run.

LeanCert proves `1 ≤ sqrt(2)` once in kernel mode in Numerics.lean. An exact
trigonometric identity and linear arithmetic give the phase-window sign
margin. All other estimates are symbolic. The six vendored transcendence
modules are compiled and axiom-audited, with retained immutable upstream
references, license and exact port diff under vendor/gotrevor-pi.

## Independent review

The two mathematical/source agents reviewed each other's components. The
coordinator compiled them; the referees do not claim independent execution.
Each report records its source/evidence hashes and excludes independently
reviewing its author's own contributions. Final reports include:

- [Complete target and all contracts](reviews/target-and-full-contracts-review.md).
- [Circulant ordering, true Hermitian interlacing and quantitative bounds](reviews/circulant-interlacing-bounds-referee-b.md).
- [Global and bulk expansion assembly](reviews/expansion-assembly-review.md).
- [Actual critical fixed-index limit](reviews/actual-fixed-index-review.md).
- [Actual inverse spectral trace identity](reviews/inverse-spectral-trace-referee-b.md).
- [Dominated spectral trace passage](reviews/spectral-trace-passage-review.md).
- [Closed-square inverse-kernel and rational trace limit](reviews/inverse-kernel-limit-chain-referee-b.md).
- [Independence from smooth extensions](reviews/extension-independence-review.md).
- [Dedicated publication workflow](reviews/publication-workflow-review.md).

Earlier exact component reviews and the pinned Tau Ceti adaptation remain
under reviews/. An agent review is informal evidence, not human peer review
or kernel replay. The main theorem supplies all three conclusions with one
coefficient family, and the hypothetical critical bound is essential to the
trace contradiction.

## Linux verification and publication

The seven names in comparator.json include both complete target theorems.
Challenge and Solution have separate import closures; Definitions.lean is
unchanged at SHA256
`35a74047a81a9b7526e9bf039880ca8f07ae33314e2b5b960ab254e02fca4b51`.
Seven deliberate Challenge placeholders are isolated from the proof.

The final check uses the repository's existing pinned Lean 4.33.1 Linux
Comparator harness, real Landrun/Bubblewrap isolation and AF_UNIX-restricted
user service. Its GitHub run ID, exact published commit and retained logs
will be reported separately. Prepared contracts, local checks and this
workflow description are not substitutes for that actual run.

This project concerns the frozen manuscript whose SHA256 is
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`.
The current upstream manuscript has a different hash; no subsequent text
or formalization is overwritten or claimed as checked here. No new problem
ID or extra distinct-problem count is introduced.

Failed development logs are retained under evidence/logs. Lean's error
recovery can print `sorryAx` in failed runs; only exit-0, source-matched
records count as passes. The superseded narrative is retained in
[VERIFICATION-HISTORY.md](VERIFICATION-HISTORY.md).
