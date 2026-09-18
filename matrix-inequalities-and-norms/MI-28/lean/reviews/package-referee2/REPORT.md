# MI-28 independent publication-package review

Verdict: **APPROVE for the bounded metadata and source-integration scope below.**
No required metadata, attribution, contract, source-preservation or evidence-path
correction was found. The root canonical-entrypoint execution and genuine final
non-root Linux GitHub checks remain pending in this reviewed package. This
review authorizes no increase to a completed-verification or mathematical-
resolution count.

Reviewer: `/root/mi28_final_referee2`, nonauthor of the MI-28 statements, proof,
and publication documentation. I previously completed the independent full
mathematical/code review of the 52-module source closure. I did not write proof
code for either task. This follow-up checks publication metadata and packaging;
it does not present a fresh compiler run as another source review.

## Exact objects reviewed

- Documentation draft: `MI28-publication-docs-draft/MANIFEST.json`, SHA-256
  `3f35c783a327e8e5b67165558dcb9fd557d0a8e3de4d1ea8324f73bfed06b31d`.
- Canonical package: `MI28-canonical-package-local365/PACKAGE-MANIFEST.json`,
  SHA-256 `5d0e6ef2afe59b57f0d3185fdf5685343a9db2d59ba5b1a97ecdeab01b160ea5`.
- Previously reviewed source: `MI28-local365-source-snapshot/MANIFEST.json`,
  SHA-256 `7054f5dd7c6bfcd03916565315495d463ccd3fc39db72fad13d19f81d389c089`.
- My previous full-source review manifest: SHA-256
  `4e6aa1e1489b13394222cf85f11f3f81fa7a7d275fe08f97651cb2527062b188`.

All paths above are relative to `/private/tmp/nla-lean-next-20260915`.
The canonical destination remains
`matrix-inequalities-and-norms/MI-28/lean`; the existing canonical README,
problem ID and original mathematical target have not been replaced.

## Required corrections and source preservation

The earlier build-metadata corrections are implemented: `defaultTargets` is
exactly `["Solution"]`, and the lock file's root name is `NLAMI28`. An actual
read-only comparison confirms that these are the only configuration changes;
all ten complete dependency objects and the Lean toolchain are unchanged.
The ordinary command documented for users is `lake build Solution`.

All 52 proof modules match the reviewed source hashes byte for byte, and the
publication `Solution.lean` reaches exactly those 52 modules through its local
import graph. No proof module imports `Challenge`. The frozen definitions,
challenge, comparator configuration, twenty headers, license and MI24 reuse
record are unchanged. All twenty metadata declarations, source-file bindings,
header hashes and source hashes agree with the approved implementation map.
The root aggregate keeps the same bytes previously compiled locally under
`NLA/MI28/Solution.lean`; checking this identity does not itself execute the
canonical entrypoint.

Frozen source comments describing the old unelaborated stage remain unchanged.
The current README explicitly identifies them as historical; the four original
plan/numerical-target/configuration records are archived byte for byte under
`history/statement-draft/`. Current maps and status records describe the
implemented proof. The older canonical solution's pre-Lean footer is likewise
identified as historical. There is no reason to mutate those frozen records.

## Mathematical scope, computation and attribution

The current description matches the previously reviewed complete canonical
positive-definite target: complex matrices in every dimension `n ≥ 1`, all real
`k ≥ 0`, and `0 ≤ p ≤ 2`; the actual determinant comparison, determinant
reality/positivity and stronger normalized log-majorization are identified.
No commutativity, bounded exponent, spectral gap or entry-size assumption has
been added. The optional semidefinite extension is correctly excluded from the
canonical target. My earlier detailed endpoint, Furuta, noncommuting-factor,
compound and spectral review remains applicable because every source is
unchanged.

The numerical note accurately identifies the one fixed half-exponent LeanCert
certificate. Its lower bound is used by the CFC domain argument; the upper
bound is co-certified, without claiming it independently carries the
mathematical proof. The metadata describes symbolic unbounded-parameter
reasoning, not a spurious finite interval computation over `k`.

George Stepaniants is credited with Department of Computing and Mathematical
Sciences, California Institute of Technology. The previous mathematical and
code authors, unchanged MI24 reuse, Mathlib/LeanCert and substantial AI
assistance are preserved. Schiffer and Forsythe are described as workflow
patterns. All plain-text, gzip-decoded and archived public payloads were
actually scanned, with no email-shaped identifier found. The separate
statement-review, proof-author, final-source-referee and documentation-author
roles are disclosed; the proof author is not presented as a final independent
proof referee. Applying the pinned Tau Ceti rubrics is not called official
engine execution or external human peer review.

## Verification claims and retained evidence

The package makes the supported local365 claim: 52 source-matched successful
module origins, with eight fresh and 44 reused modules, twenty selected
contracts and the standard three axioms. It explicitly excludes unrelated
MF14 failures in the mixed local batch. Local366's separately elaborated types,
universes and actual proof-body route are labeled local diagnostics, not
Comparator. Ordinary Lake execution, final GitHub Comparator/default-kernel/
sandbox/negative controls and exact publication-commit acceptance are not
claimed to have happened.

I actually authenticated all 264 package payload files and all 251 relocation
entries, checking both encoded and decoded hashes against originals. All 92
retained local365 original evidence files are represented. Seven archive
packets, containing 164 members, were authenticated in memory against their
original files; nothing was extracted to create another source tree. The
three derived current documents are explicitly distinguished from their
sealed originals. All 17 current Markdown links resolve, as do the main-result,
review-report and primary verification-record bindings. Historical absolute
paths are retained as command provenance, not portable reproduction commands.

The compact public refresh is the exact retained-field projection of its
hash-bound original, including the canonical blob, main commit, target PRs,
head PRs and command/exit-code observations. It is not represented as the
untouched raw refresh. Compact branch-audit records preserve external tree
hashes without pretending the bulk tree snapshots are embedded. Their dated,
visible-public, ID/path-limited search scope is explicit. I made no fresh Git
or network query. The observed mathematical solution was already merged as
PR #85; this package correctly claims a formalization, not a new resolution.

The co-located `formalization.yaml` validates against the pinned v0.4 schema.
The current JSON additions conservatively leave `whole_problem_verified`
false, `completed_original_targets` zero and GitHub Comparator not run.
Schema validation establishes metadata structure, not mathematical fidelity.

## Checks actually executed for this follow-up

1. Read the documentation author's complete `verify_documents.py`, then ran it
   as a read-only replay: exit 0, `DOC-CHECK.json` records PASS. This includes
   authenticating the saved 225 tree snapshots and does not repeat their
   original Git/API queries.
2. Wrote and actually ran my independent `verify_metadata.py`: exit 0,
   `INDEPENDENT-DOC-CHECK.json` records PASS. Its first attempt failed before any
   audit because this Python lacks `tomllib`; I replaced that dependency with
   a stricter exact single-field text comparison and reran successfully.
3. Wrote and actually ran my independent `verify_package.py`: exit 0,
   `INDEPENDENT-PACKAGE-CHECK.json` records PASS. It independently checks package
   hashes, imports, schema, archives, relocations, public-refresh derivation,
   links and privacy. It invokes no subprocess and does not mutate the package.

These checks were run from
`/Users/georgestepaniants/Research/OpenProblemsInNLA` with `python3` and the
absolute script paths. They are receipt/source/schema checks only: **I ran no
Lean, Lake, kernel checker, Comparator, Git or network command.** No proof or
sealed package was modified. The source acceptance remains the previous
independent mathematical/code verdict, supported by root's actual local
compiler evidence and still awaiting the required final Linux execution.

## Remaining gate

The root must record the actual canonical entrypoint/integration execution and
then the exact tested commit and genuine non-root Linux Comparator, kernel,
sandbox and rejection-control results. Any later source, configuration or
metadata edits require an explicit new hash/delta binding; this approval is
for the exact package manifest above. No other required correction is open
within this review's bounded scope.
