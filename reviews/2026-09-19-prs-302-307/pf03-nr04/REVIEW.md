# PRs 303 and 304 independent merge audit — 19 September 2026

Reviewer: Codex subagent `/root/audit_pf03_nr04`, not an author of either submitted proof. Recommendation: **merge both**, preserving these exact proof inputs, subject to the coordinator's repository integration checks. No correctness or trust-boundary blocker found. One optional NR-04 PDF footer correction is recorded below.

| PR | Project | Audited head | Immutable proof publication |
| --- | --- | --- | --- |
| 303 | PF-03 | `1cb23f48ef0a24cf8316d72c88e1d09a5ca68cdd` | `9625a76780183040186664100e24e0e90d8fcc7d` |
| 304 | NR-04 | `dfcba11c2e4f6d53e3603d532c799476f84a7113` | `f488b0cfe2175e5e50d439c5a4115accc4b07b6d` |

Base: `origin/main` as fetched by coordinator, `7e05bfbf`. Worktrees are `pf03/` and `nr04/` beside this report. The main checkout was not modified. Machine-readable source/evidence checks are in `audit.json`; their reproducible independent checker is `audit.py`.

## Mathematical correspondence

Both canonical README files from `## Context and notation` through the end are byte-identical to the published base. IDs, canonical paths and original targets are unchanged. New content promotes existing informal resolutions to formal verification; it does not invent a new problem or replace the mathematical question.

**PF-03:** `SymMatrix` is genuinely the symmetric subtype with inherited topology; CP means a finite real nonnegative Gram factor, rational factors quantify over every positive finite width, and the canonical negation quantifies over an order at least five. The actual final theorem constructs the witness rather than assuming a certificate premise. I traced the whole-cone quadratic zero classification into the rational-ray argument, the nonzero-minor/degree-three independence obstruction, the rational left inverse and Gram transport, and the trace-zero contradiction excluding all widths. Generic rational Fourier–Motzkin projection produces the rational halfspaces for the full real cone. Seed orthogonality makes the real factor nonnegative and supplies the Gram equality. Five zero rows preserve the rational obstruction and a continuous negative-diagonal perturbation proves frontier membership in the symmetric subtype. These interfaces close unconditionally in `Counterexample.lean`.

This construction need not produce the source manuscript's explicit order 444, strict positivity, or minimal cp-rank. Those are accurately excluded in current metadata and canonical prose; their exclusion does not weaken the original existential counterexample target. The two `run_tac` calls in `RootCertificate.lean` request checked LeanCert fixed-endpoint certificates and throw on failure. They introduce no new axiom or native shortcut. I regenerated the raw rational literals from the repository's two hash-pinned Holden JSON files without writing: exact 265,364-byte match.

**NR-04:** `distanceNine` uses actual real squared index differences; the indexing contract identifies labels 0–8 with the original labels 1–9. Factor definitions quantify over arbitrary real nonnegative matrices, including zero/degenerate columns and width zero. The upper bound is the explicit seven-column reflection factorization. I traced final bounds through Sylvester rank-nullity, transpose handling, zero-column-safe factor normalization, the actual affine column section and contact count. The section upper bound separately treats rank at most three, all nonexceptional height partitions, coincident candidates, and the remaining distinct 3-by-3 crossing case. The latter is discharged by affine-plane coordinates, an injective order key, crossing orientation and a proved nine-rectangle integer parity contradiction. No generic-position or unproved geometric premise survives into the final contracts. Contact counting derives the finite actual extreme-point hull and uses positive off-diagonals and at-most-two zero coordinates; it does not define the conclusion into an artificial section.

## Trust and execution evidence

The independent local import traversal reaches 60 PF-03 modules and 41 NR-04 modules from `Solution`. Neither closure imports `Challenge`; comments are stripped with nested-comment handling. No implementation `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, `extern` or `implemented_by` was found. Challenges are intentional isolated reference placeholders. Definitions are transparent and Comparator `definition_names` is empty. The selected 25 and 15 contracts exactly match advertised main results; only `propext`, `Classical.choice`, and `Quot.sound` are allowed. No shared checker, workflow or Lean policy file changes are in either PR.

All 61 PF-03 and 42 NR-04 Lean files, plus each project's Comparator configuration, lakefile, dependency manifest and toolchain, are byte-identical to their immutable proof publications. Current head metadata therefore cannot silently substitute another statement, dependency pin or proof. Both projects use the existing pinned Lean/LeanCert/Mathlib/checker trust infrastructure.

The coordinator freshly downloaded upstream GitHub artifacts and authenticated ZIP SHA256 against the GitHub API. I independently bound their complete `input_sha256` maps to these worktrees and inspected their logs:

| Project | Upstream run | Checked synthetic merge commit | Inputs matched | Selected transitive axiom reports |
| --- | --- | --- | --- | --- |
| PF-03 | 35425642335 | `ac8c1a2d0f8523469e4068ec20bd728e0e258952` | 274/274 | 25/25 standard-only |
| NR-04 | 35434032013 | `cd3428b1286a6b9ef3b8829dc19ddd781904ce8c` | 251/251 | 15/15 standard-only |

Both logs explicitly show successful Solution builds, exported proof bodies accepted by the default Lean kernel, and `Your solution is okay!`, exit 0. Source-lock hashes match current worktrees. Kernel replay controls reject an invalid raw proof and a quotient mismatch; Comparator/sandbox controls exit 0; actual negative fixtures reject `sorryAx` and native-decide axioms. The synthetic merge SHA is distinguished from the PR head, and complete project-input matching establishes the relevant correspondence.

I also independently checked the submitted archived fork/upstream evidence: all 234 PF-03 and 165 NR-04 recorded inputs per run hash to the immutable proof commit; only README, STATE and formalization metadata among those earlier inputs changed at promotion. Each original ZIP hashes to its recorded artifact digest and every extracted member matches its ZIP bytes. NR-04's two redacted provenance derivative hashes match the privacy manifest. This check does not authenticate the unpublished original email-bearing responses; fresh upstream evidence removes dependence on that limitation.

## Checks run

- `python3 tools/validate_problem_ids.py --base-ref origin/main`: PASS in each worktree, 217 permanent IDs.
- `python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v`: PASS in each worktree, 17 tests.
- `/tmp/pr-audit-20260919/agent-mi18/venv/bin/python tools/lean/validate_manifest.py nonnegative-and-positive-factorizations/PF-03/lean`: PASS, 25 declarations; equivalent NR-04 command: PASS, 15 declarations.
- `python3 /tmp/pr-audit-20260919/agent-pf03-nr04/audit.py`: PASS, detailed checks and inputs in `audit.json`.
- `python3 nonnegative-and-positive-factorizations/PF-03/lean/generate_raw_data.py --data-dir references/holden-pf03-2026-09-13/data`: MATCH, no write; SHA256 `6c2aadd80f167fd15fb28543d1578ca4a64a16a090ab02660d23f46e993ea02d`.
- Read-only Poppler `pdfinfo`, `pdftoppm -scale-to 1800 -png`, and `pdftotext -layout` on both canonical PDFs: two A4 pages each. All four page images inspected.

The default and bundled Python interpreters initially lacked `jsonschema`; validation was completed successfully using the shared audit venv. An initial guessed `check_manifests.py` filename was absent; the actual repository validator above was found and passed. No new local Lean build is claimed; authoritative fresh Linux executions and their exact source binding supply execution verification. This is a bounded source/architecture/trust audit, not a second independent recreation of every arithmetic proof or external human peer review.

## PDF inspection

All four pages are legible, with no clipped/overlapping text, broken mathematical glyphs, missing original statement, or truncated quantifiers. PF-03 keeps the original target together on page 2 and clearly distinguishes formal witness scope from manuscript extras. NR-04's real factors and six-versus-seven question remain explicit. Headers, page numbers, links and references are intact. Renders and extracted text are under `pdf/` beside this report.

Minor editorial observation: NR-04 footer says `Literature check: 2026-09-19` although that date records formal verification and its retained literature-search section is dated 2026-09-10. PF-03 correctly says `Verification check`. Suggested optional integration correction: add NR-04 to the existing verification-label allowlist in `tools/render_problems.py`, regenerate its TeX/PDF, and inspect again. This has no mathematical or proof-trust consequence.
