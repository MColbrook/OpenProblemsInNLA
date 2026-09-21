# MF-21 frozen manuscript: publication evidence

This submission formalizes the unchanged 12 September manuscript. It supplements
the existing MF-21 formalization and adds no new problem or distinct-problem count.

George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology. Substantial AI assistance is disclosed;
original mathematical and library authorship is retained. The independent
reviews below are AI-agent reviews, not external human peer review.

## Exact source and mathematical scope

The [immutable proof project](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/fe2183e9b570322d7c1f64bba3480460082af8d3/matrix-functions-and-stability/MF-21/lean-frozen-2026-09-12)
is at `fe2183e9b570322d7c1f64bba3480460082af8d3`. The retained original
manuscript has SHA256
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`.
Neither the canonical mathematical statement nor that manuscript was changed.
The current upstream manuscript and existing Lean project are preserved.

[Source-identity checks](september12-source-identity.json) confirm that this is
the original September 12 commit, not a later manuscript retaining that date.
All 43 displayed formulas also match that commit's standalone TeX source after
whitespace normalization.

`MF21Restart.Contracts.target_proved` proves the complete original three-part
target for every integer `m ≥ 3`. One coefficient family supplies every global
order through `2m-1`, the critical order on the original logarithmic bulk range,
and failure of a global critical bound. The matrices are the actual
integral-defined Toeplitz matrices; all original eigenvalue indices remain.
`MF21Restart.Contracts.manuscript_smooth_target` also establishes the manuscript's
smoothness. Five additional contracts check the Fourier correspondence and
analytic prerequisites. No necessary premise is left unproved.

## Local Lean evidence

The project pins Lean 4.33.1, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`. LeanCert's single scale-zero
square-root certificate is checked in kernel mode. All other estimates are
symbolic.

The complete 125-source run passed, then the final phase tactic adjustment
received a recheck of its entire affected dependency closure: 10 actual
compilations and 115 source/output/dependency-validated reused outputs.
All 386 actual axiom reports matched and used only `propext`, `Classical.choice`
and `Quot.sound`. The [phase recheck audit](phase-recheck-evidence-review.md)
independently confirmed that exact scope. The project retains the original
commands, logs, source hashes and output hashes. No additional compiler run
is inferred from a metadata or hash check.

With pinned dependencies and their cache materialized, the local reproduction
command in the proof project is `python3 verify_local.py`. It serializes Lean
with one thread and a 4096 MiB cap. Ordinary Lake builds allow 6144 MiB; this
higher library setting also applies to an ordinary local `lake build`.

## Separate Linux verification

The [successful run 35552653565](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35552653565)
checked the exact immutable proof revision above on a non-root Linux runner.
The actual [result record](linux-attempt-03/verify-20260921T020023Z-4146/result.json)
reports `comparator-accepted` for all seven contracts. The target's
[Comparator log](linux-attempt-03/verify-20260921T020023Z-4146/comparator.log)
records both `Lean default kernel accepts the solution` and
`Your solution is okay!`, followed by exit status zero. The allowed transitive
axioms are only `propext`, `Classical.choice` and `Quot.sound`.

The [download receipt](linux-attempt-03.json) identifies actual GitHub artifact
`10619061816`. All 1,423 recorded input hashes match both the published proof
commit and the retained project. Its actual sandbox probes, default-kernel
controls, Comparator regression controls, and rejection of sorry/native trust
are retained alongside the target log. This is separate Linux execution, not
an inference from local compilation or a checker-fixture success.
The [independent operational review](linux-operational-review.md) records its
own authenticated run/artifact and source comparisons.

The earlier attempts [35548010081](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35548010081)
and [35550709155](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35550709155)
failed during project compilation. Their actual artifacts are retained under
`linux-attempt-01/` and `linux-attempt-02/`, with separate receipts. Successful
checker fixtures in those runs do not constitute acceptance of the MF-21 target.

## Independent review and publication documents

The explicit manuscript comparison is recorded separately for
[Sections 2–3](original-proof-reaudit-sections2-3.md) and
[Sections 4–5](original-proof-reaudit-sections4-5.md). These audits found no false
step in their stated scopes. They distinguish the written text from its formal
implementation: Lean expands the recurrence-to-kernel correspondence, uses
some weaker sufficient estimates, proves coefficient vanishing by factoring a
power, and proves the cited inverse-kernel result from the exact finite inverse.
The trace limit then follows by uniform grid convergence and Riemann sums.
These are proof expansions and reorganizations, not a literal transcription
of every sentence. The descriptive Green-operator characterization is not
separately formalized. Both the September 12 theorem and this project's target
concern the same constructed coefficient family; no stronger theorem about
every alternative coefficient family is claimed here.

A separate [fresh mathematical audit of the entire September 12 manuscript](fresh-september12-mathematical-review.md)
independently reconstructed its main derivations and checked its cited kernel
input without using previous reviews, later manuscript versions, or compiler
acceptance as evidence. It found no mathematical error in the stated theorem.
This is an informal mathematical review, not an additional Lean run or a
certification of every prose sentence.

The proof project retains component, full-target, statement and proof reviews
under its `reviews/` directory. Two final referees did not implement the proof.
Their bounded scopes and exact source hashes are explicit. The subsequent
[phase repair review](phase-memory-repair-review.md) and
[publication metadata review](final-publication-metadata-review.md) cover the
final edits and distinguish actual local execution from the then-pending Linux
evidence. The subsequent operational review covers the completed Linux run.
[Source binding](final-source-binding.json) records the unchanged proof inputs,
original target, registry, indexes and older formalization.
The final [publication source check](publication-source-binding.json) reconfirms
all 1,423 proof-project files against the accepted commit and records the hashes
of the subsequent manuscript-comparison and operational reviews.

The unchanged repository renderer regenerated MF-21's canonical documents in
[run 35552753810](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35552753810).
Its [artifact receipt](catalog-render-03.json) binds the exact source and output
hashes. All three final PDF pages passed [visual inspection](catalog-visual-review-03.json).
The earlier clipped draft is retained as a failed layout review, not the final
PDF. The temporary rendering workflow is removed from the submitted repository.

[Catalog checks](catalog-checks/record.json) record successful permanent-ID
validation, index regeneration with no count changes, and all 17 safeguard
tests. This submission requests inclusion through its own upstream pull request.
