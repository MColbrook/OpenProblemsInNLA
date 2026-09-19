# Audit and integration of PRs 302, 303, 304, 306 and 307

Date: 19 September 2026. Reviewers: coordinating Codex agent and three separate
Codex audit agents. These are AI reviews, not external human peer review.

The audit starts from published main `7e05bfbf97427c558606884172cafd0764ebdc20`.
The requested heads are retained as ancestors of this integration:

| PR | Target | Audited head |
| --- | --- | --- |
| 302 | MF-08 literature resolution | `4af381c0fe300f79d422a938c8141c80a0daaa73` |
| 303 | PF-03 rational-factor counterexample | `1cb23f48ef0a24cf8316d72c88e1d09a5ca68cdd` |
| 304 | NR-04 nonnegative rank seven | `dfcba11c2e4f6d53e3603d532c799476f84a7113` |
| 306 | MI-27 coefficient-one bound | `1f05b398013d44beb7d756cbfbbfd3e875c8deab` |
| 307 | MI-18 order-four partial result | `8a59a746c01273448875f61239d4481437b69590` |

## Findings and integration repairs

No blocking mathematical or proof-trust finding was identified in the recorded
review scopes. The catalog summaries conflict or silently retain stale totals
when independent status changes are merged. They were regenerated from the
canonical pages after permanent-ID validation. All 217 IDs, their paths, and
their original mathematical targets are preserved.

MF-08's two versioned arXiv theorems quantify over unrestricted real gains and
strict Hurwitz stability, with integer input matrices and polynomial-time
reductions. Encoding each integer with denominator one embeds either subclass
in the retained rational-input question. The coordinator authenticated the
current version records and theorem statements in
[Löfberg, Theorem 1.1](https://arxiv.org/html/2609.16886v1) and
[Ahmadi et al., Theorem 1](https://arxiv.org/html/2609.20636v1), and read the latter's
complete continuous-time proof (Lemmas 2–4 and the reduction). The Lyapunov
identity, unbounded-real-gain converse, preserved diagonal entries, and
polynomial-size integer construction support the claimed applicability.
A separate reviewer also read Löfberg's complete proof and appendix, checking
the global unbounded-gain estimates, frequency separation, realization, and
binary-size bounds; see the [supplement](mf08-supplement.md).
No NP-membership or external peer-review claim is added. The original statement
and historical audit remain unchanged; both canonical PDF pages were inspected.

The PF-03 and NR-04 source review checks the actual definitions, complete final
theorems, independent challenge boundary, pinned dependencies, and proof trust.
The official upstream artifacts reproduce all 274 PF-03 and 251 NR-04 input
hashes, respectively. Their 25 and 15 selected theorem checks passed real
Comparator, default-kernel replay, standard-axiom checks, sandbox controls, and
deliberate rejection tests. This audit authenticates those Linux executions;
it does not claim a fresh local Lean rebuild. See the [retained source review](pf03-nr04/REVIEW.md).

MI-27's PR description still called Linux verification pending, but actual
[upstream run 35438172834](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/35438172834)
had succeeded. Its artifact digest was authenticated, all 284 inputs match the
audited head, and all 20 contracts and operational controls passed. The executed
synthetic merge has the published base and that exact head as parents; this is
recorded without conflating the checkout commit with the source head. Publication
metadata was updated after the [separate source and evidence audit](mi27/REPORT.md),
and the regenerated two-page canonical PDF was visually inspected. The NR-04
PDF footer now correctly labels its date as a verification check; both regenerated
pages were inspected. The final catalog has 62 Lean verified and 44 other Solved
entries, with 41 Open and 70 Partially resolved entries (111 open targets).

MI-18's two exact verifiers, twelve deliberate corruption rejections, tensor
addendum, archive manifests, and regenerated data pass. The separate
[mathematical and executable audit](mi18/audit.md) covers complex Hermitian PSD
matrices, degeneracies, fixed inversion order, rank reduction, strictness, and
the order-four scope. The arbitrary-order question remains Partially resolved.
Its certificates are not described as proof-assistant verification or a priority
certification. All proof, audit-report, and canonical PDF pages were inspected.

## Verification and evidence

The small official PF-03 and NR-04 artifact archives and API digest records are
retained in `ci/`; MI-27's Linux evidence is retained with its project. Digests:

- PF-03 artifact 10578243778, run 35425642335:
  `46cfcc44dab0fc84dfafd1c1997109f5efb5f2e18071e8c9f6c10d8625ca2d53`.
- NR-04 artifact 10581187527, run 35434032013:
  `89ff99157242551db6980949d8837ab9710e711dbad93738710ea13982cd923d`.
- MI-27 artifact 10583511156, run 35438172834:
  `50394e222707d250e7e1fc58dc80b8f6e59fb475b324a3414fd59f36e045b094`.

The final integration is subject to the normal protected-branch checks and fresh
Linux verification of exactly MI-27, NR-04 and PF-03 before merging. No branch
protection, validator, checker, workflow, or theorem contract is weakened.
The small renderer changes concern publication layout and date labels only.

Local repository and harness test outputs are retained alongside this report:
77 repository tests and 12 harness tests passed, including all 17 permanent-ID
regressions and the Pandoc mathematics-conversion tests.
Proof review does not certify every unrelated source-context archive or future
dependency version; immutable pins and verified source correspondence delimit
the accepted scope.
