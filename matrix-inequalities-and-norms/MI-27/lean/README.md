# MI-27: coefficient one in the logarithmic commutator inequality

Formalization by **George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology**, with substantial Codex assistance. The analytic resolution remains credited to **Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation**.

`NLA.MI27.logarithmic_commutator_bound` proves the unchanged original inequality for every positive dimension and every complex positive definite pair with trace sum one. It uses the actual spectral natural logarithm and Gram-square-root trace norm. Neither the relative-entropy identity nor its derivative is assumed in the final theorem. The source manuscript's separate order-two optimality result is not included in the advertised formalization.

## Verification status

All twenty frozen contracts pass actual local serial Lean in recovery-118. The [recursive local audit](verification/local-2026-09-19/LOCAL-REPLAY-AUDIT.json) binds 52 proof modules, actual commands, source/output hashes and successful source-matched dependency reuse. The coordinator allows only one compiler, one thread and 4096 MiB. The [transitive axiom reports](verification/local-2026-09-19/actual-axioms.json) contain only standard Lean axioms. An [isolated local diagnostic](verification/type-preflight-118/AUDIT.json) found all twenty elaborated types and universe lists byteidentical to the frozen Challenge.

Two wholly nonauthor final source reviews passed: [referee B](reviews/final-referee-b/REPORT.md) and [newmath referee](reviews/final-newmath/REVIEW.md). Each independently authenticated the actual saved local evidence without rerunning the compiler. Actual [non-root Linux run 35438172834](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/35438172834) passed Comparator, default-kernel replay, standard-axiom, sandbox and rejection controls for all twenty contracts. The PR merge checkout `f21284e35e8156a9761c1f2ccd49d579f42fb69a` has all 284 project inputs identical to immutable head `1f05b398013d44beb7d756cbfbbfd3e875c8deab`; [retained logs and source authentication](verification/linux-2026-09-19/README.md) bind that result. This completes the original upper-bound target and supports canonical Lean verified status. Subsequent publication edits require separate CI. [STATE.md](STATE.md) and [STATE.json](STATE.json) record the current phase; historical frozen snapshots remain unchanged.

## Proof structure and computation

The proof derives a dimension-independent positive-commutator bound, an endpoint-optimizer bound along actual unitary flow, and one cutoff valid for all unitary conjugates. It proves the ordinary noncommuting relative-entropy identity internally using negative spectral counts, congruence invariance, scalar pencil integration and Fubini with prior integrability. Mixture terms are truncated before substitution. Finite kernel integrals then bound entropy change; the actual noncommuting trace derivative and a spectral-sign witness give coefficient exactly one. Repeated eigenvalues, zero commutators and the degenerate finite interval remain included.

Kernel-mode LeanCert proves only the fixed exact inequality `0 < 1/2`, consumed in the positive-commutator argument. There are no interval variables, subdivisions or numerical quadratures. Every exported theorem also passes `#assert_trust kernel`. The twenty deliberate reference placeholders in `Challenge.lean` are never imported by the proof environment. Seven retained MI24 modules support the proof and do not count as an additional formalized problem.

The [numerical plan](NUMERICAL_TARGETS.md), [implementation map](IMPLEMENTATION-MAP.json), [metadata](formalization.yaml), frozen contracts and source context document the full scope. The proof's C10 cutoff is R=1+M/epsilon with M=norm(rho)+norm(sigma)+1; this sound construction proves the unchanged existential contract and supersedes the plan's simpler suggested cutoff.

## Reproduction

Inside this directory, with the pinned Lean 4.33.1 toolchain:

```sh
lake build Solution
```

This is the usual standalone build command; the recorded macOS development runs instead use the retained direct serial Lean commands with one thread and 4096 MiB. All dependencies are pinned. For final Comparator, follow the non-root Linux isolation setup in [the workflow](../../../.github/workflows/lean-verification.yml), then from the repository root run:

```sh
tools/lean/bootstrap.sh /tmp/mi27-lean-tools
tools/lean/verify.sh matrix-inequalities-and-norms/MI-27/lean /tmp/mi27-lean-tools
```

The pinned Tau Ceti rubrics inform AI-agent review; no official Tau Ceti execution, human peer review or source-author endorsement is claimed. Schiffer and Forsythe supplied inspected statement/workflow patterns, not imported mathematical results. The retained Linux evidence identifies its actual checkout and exact source hashes. Later publication or merge runs are distinct executions and must not be inferred from that earlier pass.
