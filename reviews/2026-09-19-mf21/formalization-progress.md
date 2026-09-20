# MF-21 formalization progress — 20 September 2026

The complete proof is implemented in the canonical project
[`MF-21/lean`](../../matrix-functions-and-stability/MF-21/lean/README.md).
The local proof commit is `e378ec4679f9119aacf79a0fe30b80493a61ec5b`.
No push or GitHub PR creation has occurred. The user requires complete
verification before PR readiness and explicit permission before any push.

## Completed proof scope

`Solution.lean` exports the full all-`m ≥ 3` three-part target, the stronger
obstruction for every continuous coefficient family, one smooth common
family with all original estimates and sharp finite-head/global error bounds,
the exact Fourier-integral matrix correspondence, and coefficient uniqueness.
No spectral, root, trace-limit, uniformity, coefficient-existence or
transcendence premise remains unproved in these exports.

The proof constructs the actual stable roots and smooth phase, proves the
normalized determinant equation and its derivative/endpoint estimates,
indexes its roots against the actual Hermitian eigenvalues, constructs the
common Taylor family, and obtains the uniform estimates. A direct finite
inverse-column formula and Schur recurrence establish the rational actual
trace limit. The shifted zeta evaluation and a fully imported proof of
transcendence of pi establish the irrational model trace. The trace mismatch
gives an eventual fixed-finite-head lower bound. Uniqueness on the exact
logarithmic-squared mesh rules out every competing continuous family.

The manuscript equation (24) now uses the finite-head Taylor argument that
was formalized; equations (26)–(29) now include the direct finite trace proof.
The final nine-page proof PDF and three-page problem PDF were rebuilt and
visually inspected after the verification note and final wording changes.

## Completed developer checks

- All 82 canonical proof modules compiled with Lean 4.33.1 and `--trust=0`
  into an initially empty output directory. No existing local project oleans
  were used.
- The generated audit inspected the transitive axiom closure of all 1,354
  local declarations, including generated/private declarations. Only
  `propext`, `Classical.choice`, and `Quot.sound` occur.
- Challenge compiled separately with exactly its five deliberate specification
  placeholders; it is absent from the Solution import closure.
- The five-result v0.4 metadata manifest passes schema and comparator-coverage
  validation. Permanent-ID validation passes for all 217 registered IDs.
- An isolated local Ubuntu ARM VM was provisioned without shared host
  directories. The pinned Linux harness bootstrap and full selftest passed,
  including real sandbox isolation and the sorry/native-trust negative controls.

See [fresh source replay evidence](verification/canonical-source-replay/) and
[Linux infrastructure evidence](verification/linux/). The macOS replay trusts
external pinned dependency oleans; missing cleaned-up external Git metadata
is explicitly recorded. The Linux run obtains fresh dependency checkouts.

## Completed acceptance

The actual project Comparator run accepted all five contracts at the stated
local commit. Lean's default kernel accepted the exported solution, and all
required sandbox and negative controls passed. Two independent nonimplementing
AI-agent referees approved the formal statement/source correspondence and the
proof; their combined explicit close-reading scopes cover all 83 local Lean
files, including Challenge. The proof referee independently inspected the
actual Linux receipt, all 96 input hashes and archives, all 251 printed axiom
reports, exact configuration and control outcomes.

The [canonical Linux evidence](../../matrix-functions-and-stability/MF-21/lean/verification/linux-2026-09-20/README.md)
records the immutable checked input snapshot. Later publication changes update
only README/metadata and add evidence/review/rendered files; all mathematical
and build inputs stay byte-identical to the accepted revision. The final
publication comparison makes these differences explicit.

The historical development source archive and scoped author/cross-reviews
remain in this directory. The canonical `reviews/packaging-map.json` records
source hashes before and after the mechanical import migration. The local
branch has not been pushed and no GitHub PR was created.
