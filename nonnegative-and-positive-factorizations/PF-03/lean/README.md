# PF-03: rational factors on the completely positive boundary

**The complete target passes local Lean checks and two independent source reviews.**
The published-source Linux Comparator check is pending. The canonical
status remains Solved until those gates finish. See [STATE.json](STATE.json)
and [formalization.yaml](formalization.yaml).

The formalized result is the complete negative answer to the retained
[PF-03 question](../README.md): some rational symmetric completely positive
boundary matrix of order at least five has no nonnegative rational Gram factor
of any positive finite width. Boundary is taken in the real symmetric-matrix
space. The final declarations are
`NLA.PF03.pf03_counterexample` and `NLA.PF03.canonical_negative_answer`.

Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons
Foundation, retains the original mathematical and exact seed-data authorship.
George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, contributes formalization and proof
engineering with substantial Codex assistance. Source credits remain in the
component files. No external human peer review or source-author endorsement
of the formalization is claimed.

## Project and scope

`Solution.lean` imports only the implementation and requests axiom and
kernel-trust checks for all 25 frozen contracts. It is the default Lake target.
`Challenge.lean` is a separate trusted reference environment with 25 deliberate
proof placeholders; it is never imported by the solution. The byte-identical
frozen `comparator.json` compares all 25 declarations, allows only the three
standard foundational axioms and has no replaceable definitions.

The [implementation map](IMPLEMENTATION-MAP.json) identifies every contract.
The [numerical plan](NUMERICAL_TARGETS.md), frozen definitions and Challenge
retain their reviewed historical bytes, including draft-status comments;
current status is in STATE.json. The statement gate was approved by two
agents before proof implementation. Those agents later authored proofs, so
two different nonauthors conducted the final proof reviews.

The implementation replaces facet enumeration and the explicit order-444
matrix expansion with a proved rational Fourier–Motzkin halfspace
representation and five zero-row padding. This proves the same original
universal assertion false. The source's additional explicit-order,
strict-entry-positivity and minimal real cp-rank claims are outside this scope.

Only three fixed root-endpoint inequalities use kernel-mode LeanCert. Exact
cubic arithmetic, symmetry and a checked reusable QG product keep the other
certificates small. Cone geometry, unrestricted factor width and the boundary
argument are symbolic. No narrowed interval domain or unproved certificate
premise is introduced.

## Reproduction and evidence

The project pins Lean 4.33.1, LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`, and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474` in the committed Lake files.
The standard project build target is `lake build Solution`; this package
does not yet claim that a standalone Lake build was run. The campaign uses
one serial local compiler process, one thread and a 4096 MiB limit, with
source-matched pinned dependency outputs.

The [actual local audit](verification/local-2026-09-19/LOCAL-REPLAY-AUDIT.json)
authenticates the 59 implementation modules, their original successful commands,
and the fresh Solution aggregate in recovery-047. It retains lossless original
receipts and checks every reused source, transitive source, log and output hash.
The [aggregate log](verification/local-2026-09-19/logs/recovery-047/Solution.log)
reports only the three standard foundational axioms for all 25 contracts;
all 25 kernel-trust assertions passed. This is a macOS local check, not the
Linux Comparator/sandbox check. The [packaging snapshot](PACKAGING-SOURCE-SNAPSHOT.json)
is a separate earlier source-copy observation, not another compiler run.
The independent final reviews are [referee 2](reviews/final-referee2/REVIEW.md)
and [referee 3](reviews/final-referee3/REVIEW.md). A
[supplementary review](reviews/final-referee1/REVIEW.md) by an earlier definitions
author is retained separately and excluded from the two-reviewer independence
count. These AI-agent reviews inspected source and actual local evidence; they
did not rerun Lean or Comparator. Published-source GitHub verification remains
pending.

Final review applies the repository's pinned Tau Ceti guidance manually. This
does not represent official Tau Ceti service execution. Local Lean checks and
GitHub Comparator checks are recorded separately. The [consolidation notes](PACKAGING-NEXT-STEPS.md)
list the evidence still required before promotion or publication.
