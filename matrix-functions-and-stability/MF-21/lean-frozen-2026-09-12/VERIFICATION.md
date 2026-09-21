# MF-21 verification evidence

This is the evidence snapshot before the repaired source's Linux run, dated
21 September 2026 UTC. Subsequent publication evidence is linked from the
canonical MF-21 problem page and does not retroactively change these records.

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
The historical [125-source integration run](evidence/runs/20260921T000301098707Z/record.json)
passed from `2026-09-21T00:03:01.098707+00:00` to
`2026-09-21T00:18:29.089795+00:00`, with all 386 expected axiom reports.
Its record SHA256 is
`abdf520ffbcfc2fe80236e0c303795d97a50e8c11f46a5edbac8a29dba5d7856`.
Every source, dependency pin, log and compiled-output hash was checked again
against that record with no mismatch before the subsequent repairs below.
That run used the archived earlier Numerics and Lake configuration; it is not
source-matched evidence for those two repaired files. The earlier 112-module
record predates final assembly and is retained only as history.

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

The numerical implementation was subsequently reduced to the scale-zero
rational square-root certificate described in
[NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md), without changing its statement.
The [isolated local candidate check](evidence/logs/numerics-minimal-candidate-02.json)
passed with the repaired source SHA256
`c4677460fab467e2992c9fd0b1d74abf0d682ba8a7c89857d77e2b481a89e410`,
one thread, a 4096 MiB cap, a kernel-only LeanCert trust assertion and only the
three permitted axioms.

The repaired project's [complete 125-source integration run](evidence/runs/20260921T005811719722Z/record.json)
then passed from `2026-09-21T00:58:11.719722+00:00` to
`2026-09-21T01:13:32.503384+00:00`. Its record SHA256 is
`497c98bffe6628a5adef5653adfb73cf25e04fd27f7306176aea9e34260842c5`.
All 125 invocations returned zero, all 386 expected axiom reports matched,
and every source, pin, runner, manuscript, log and compiled-output hash was
checked against the retained record. The [integrity receipt](evidence/repaired-full-run-integrity.json)
records that comparison. This run includes both the minimal numerical
certificate and the six-root Lake configuration. It is local Lean evidence,
not a Linux Comparator or sandbox acceptance.

The subsequent [phase-source recheck](evidence/runs/20260921T014829335357Z-phase-recheck/record.json)
passed from `2026-09-21T01:48:29.335357+00:00` to
`2026-09-21T01:50:06.082402+00:00`. Its record SHA256 is
`bcb21102dcd847a244595c04f6cd759b7221b4bd0c0e674beef969ed6eea9c3a`.
This was 10 actual recompilations covering PhaseWindowRoots and all its local
dependents, including TargetProof, Solution and Audit. The other 115 outputs
were reused only after matching their source, output, log and dependency
hashes against the preceding successful run. All 386 actual axiom reports
matched again. This is not another 125-invocation build. The commands still
used one thread and a 4096 MiB cap; the current library configuration's higher
ordinary-Lake limit does not alter the local runner.

## Independent review

The two mathematical/source agents reviewed each other's components. The
coordinator compiled them; the referees do not claim independent execution.
Each report records its source/evidence hashes and excludes independently
reviewing its author's own contributions. Final reports include:

- [Complete target and all contracts](reviews/target-and-full-contracts-review.md).
- [Nonimplementing final statement referee](reviews/independent-final-statement-review.md).
- [Nonimplementing final proof and trust referee](reviews/independent-final-proof-review.md).
- [Unchanged phase statements and resource-only Lake repair](reviews/phase-memory-repair-review.md).
- [Independent audit of the 10-compilation, 115-reuse recheck](reviews/phase-recheck-evidence-review.md).
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

The two final referees did not implement any part of this proof. They approved
statement fidelity and the selected proof-assembly/trust scopes, including the
repaired numerical source. Their reports identify exactly which sources were
read; neither report claims an independent compiler or Linux execution, nor
a fresh line-by-line review of every lower-level module.

## Linux verification and publication

The seven names in comparator.json include both complete target theorems.
Challenge and Solution have separate import closures; Definitions.lean is
unchanged at SHA256
`35a74047a81a9b7526e9bf039880ca8f07ae33314e2b5b960ab254e02fca4b51`.
Seven deliberate Challenge placeholders are isolated from the proof.

The first [published Linux attempt](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35548010081),
at commit `e6f038f48b3039df030237424c05be745e33ce24`, failed during the
project build. Lake had not registered five sibling transcendence modules,
and the earlier Numerics build terminated with an interpreter memory exception
under the 4096 MiB cap. The log does not isolate the cause of that memory use.
It did not produce target Comparator or default-kernel acceptance. Negative
control successes in that run do not count as acceptance of the MF-21 proof.

The repaired Lake configuration explicitly registers all six vendored
transcendence modules, and the smaller numerical certificate preserves the
same exported theorem. See [module-registration evidence](evidence/lake-registration-fix.json)
and [numerical repair evidence](evidence/numerics-minimal-certificate.json).
The failed run remains recorded as failed; a successful new Linux execution
is still required.

The second [published Linux attempt](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35550709155),
at commit `bd3014e699f277500beabda57cfeb1f57925ab78`, built the repaired
Numerics and registered transcendence modules successfully, then failed in
PhaseWindowRoots with an interpreter memory exception under the 4096 MiB cap.
It likewise produced no target Comparator or default-kernel acceptance.

Twelve arithmetic tactic calls in PhaseWindowRoots now name their sufficient
hypotheses explicitly; no theorem statement or mathematical argument changed.
Both old and new versions passed isolated local checks, with approximately
3.65 GB peak resident memory. The measurements do not establish a material
memory reduction. Four ordinary-Lake library limits were therefore raised
from 4096 to 6144 MiB for the next Linux run. These limits also apply to an
ordinary local `lake build`; `verify_local.py` remains explicitly capped at
4096 MiB. No contract, dependency, trust setting or sandbox restriction changed.
See the [repair record](evidence/phase-memory-diagnostics/repair.json) and the
two scoped independent reviews above. Linux acceptance remains a separate
required execution.

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
