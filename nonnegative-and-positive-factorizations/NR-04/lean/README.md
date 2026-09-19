# NR-04: the nine-point distance matrix has nonnegative rank seven

Formalization by **George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology**, with substantial Codex assistance. **Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge**, retains original mathematical authorship. The reflection construction retains the source's Hrubeš and Gillis–Glineur attribution.

The final theorems `NLA.NR04.nine_point_nonnegative_rank_seven` and `NLA.NR04.canonical_six_factor_impossible` settle the unchanged original target over arbitrary real nonnegative factors. The indexing theorem identifies Fin9 differences with the original labels 1 through 9. All widths are included in the lower bound, including zero and degenerate factor columns.

## Verification status

All 15 frozen contracts passed actual local serial Lean in recovery-086 and the publication-name aggregate in recovery-087. The [source and reuse audit](verification/local-2026-09-19/LOCAL-REPLAY-AUDIT.json) authenticates 41 proof modules, their actual commands, logs, output hashes and successful dependency-matched reuse origins. The coordinator allowed one compiler, one thread and 4096 MiB. The archive script itself ran no Lean. Only `propext`, `Classical.choice` and `Quot.sound` occur in the [actual transitive reports](verification/local-2026-09-19/actual-axioms.json).

Two wholly nonauthor AI-agent final source reviews passed: [referee A](reviews/final-referee-a/REPORT.md) and [referee B](reviews/final-referee-b/REPORT.md). The real published-source Linux Comparator/default-kernel/sandbox checks remain pending. The canonical status remains Solved and this package does not yet increase the completed-verification count. Historical frozen statement comments are retained as evidence of the pre-proof phase; `STATE.json` records the current phase.

## Proof structure and computation

An exact seven-column reflection factorization supplies the upper bound. The lower bound normalizes arbitrary factors, proves a geometric section contact bound, and applies a fully proved rank-nullity form of Sylvester's inequality to both factors. A separating affine key and a nine-grid crossing-parity obstruction prove the exceptional planar bound. The proof avoids enumeration of all point orderings and never substitutes a rational search for arbitrary real factors.

Kernel-mode LeanCert certifies the fixed inequality `0 < (8 : ℝ)`, consumed by the exact ordinary-rank determinant argument. There are no interval variables or subdivisions. Every exported contract additionally passes `#assert_trust kernel`. The independent `Challenge.lean` has 15 deliberate statement placeholders; it is never imported by `Solution.lean`.

## Reproduction

Inside this directory, run:

```sh
lake build Solution
```

The Lean 4.33.1 toolchain and all dependencies are pinned. The recorded macOS development evidence uses direct serial Lean commands; no standalone local Lake build is claimed. GitHub runs the repository's real non-root Linux Comparator. Its exact commit, run IDs and retained artifacts must be recorded separately before promotion.

The [15 statement-first contracts](NUMERICAL_TARGETS.md), [implementation map](IMPLEMENTATION-MAP.json), [metadata](formalization.yaml) and independent review reports retain their precise scopes and source hashes. The pinned Tau Ceti guidance informs AI-agent reviews; no official Tau Ceti service, human peer review or source-author endorsement is claimed.
