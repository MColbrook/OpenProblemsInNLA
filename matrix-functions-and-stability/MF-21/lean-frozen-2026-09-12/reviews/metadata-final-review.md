# Final metadata and reproduction consistency review

Verdict: **APPROVE within the metadata, provenance, local-evidence, and reproduction scope stated here.** No remaining material misstatement of the mathematical target or executed local verification was found. The final GitHub Comparator/kernel/sandbox check remains unrun and is not approved as successful by this report.

Reviewer: `mf21_restart_lean_audit`, using the pinned Tau Ceti adaptation, SHA256 `e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`. No Lean compiler or Comparator was started by this reviewer. The mathematical Target/contract review is separate in `target-and-full-contracts-review.md`; this report does not expand its independent proof-review scope.

After independently identifying the reproduction issues, this reviewer implemented the coordinator-authorized lock portability change, removed the plain Lake shortcut from README, and wrote/executed the Python-only smoke check. Those small edits and their tests are **not independently reviewed contributions of this reviewer**. Their exact scope and evidence are disclosed below for the coordinator's inspection. All other proof sources remained unchanged.

## Current claims and requested workflow

| Requirement | Inspected evidence and finding |
|---|---|
| Preserve the original mathematics and target | `original-proof/solution.md` is byte-identical to the original commit; `problem.md` is the exact canonical snapshot used for source review. Target still has all three assertions for every `m≥3`, one family, the actual Toeplitz spectrum, and one-based indices. No proof replacement, problem renumbering, or extra distinct-problem count is claimed. |
| State obligations before proving them | `STATEMENTS.md`, the component locks, `TARGET_ASSEMBLY_STATEMENTS.md`, and `COMPARATOR_TARGET_STATEMENTS.md` identify the exact obligations. The current summary correctly reports their later completion; the preserved historical files remain historical. |
| Kernel-mode LeanCert | `Numerics.lean` explicitly sets `leancert.trust` to `"kernel"` and calls `interval_decide (trust := kernel)`. Its closed residual is `1≤sqrt(2)`, followed by an exact trigonometric identity and linear arithmetic. |
| Minimize computation | `NUMERICAL_TARGETS.md` correctly records one closed inequality, no interval subdivision, numerical integration, or matrix enumeration, and reuse of that certificate. The parameter-dependent estimates are symbolic. |
| Independent review with exact scopes | The final reports record hashes and exclude each reviewer's own proofs. The Target assembly and the interlacing dependency chain have different reviewers. The metadata expressly identifies AI-agent review and does not claim human peer review or independent compiler execution by the referees. |
| Exact Comparator contracts and separate final execution | All seven advertised `main_results` occur exactly once in `comparator.json`; both complete theorems are included. Only the three standard axioms are permitted. Seven intentional Challenge theorem placeholders are isolated from Solution. The fresh Linux Comparator and sandbox/kernel checks are described as a separate future run, not inferred from local success. |
| Truthful formalization metadata and attribution | The current v0.4 metadata has a source-matched successful schema/coverage record. George Stepaniants and the Department of Computing and Mathematical Sciences, California Institute of Technology, are credited; AI assistance and original/library authorship are retained. No contact email is included in those attributions. |

`README.md:3–18`, `STATEMENTS.md:7–17`, and `formalization.yaml` correctly say that the complete Target and the stronger same-family smooth theorem passed locally. `ContDiffAt ℝ ∞` is the actual smooth conclusion, not an inaccurately described analytic assumption. The claims that all prerequisites are discharged and all original eigenvalue indices are covered agree with the reviewed final assembly. The spectral comparison still has the exact `h^(2m) j^(2m-1) exp(-cj)` factor only for `j≥J`; the Taylor remainder has no exponential factor.

`VERIFICATION.md:11–36` distinguishes the individual Target test, wrapper/preflight tests, and complete integrated run. `VERIFICATION-HISTORY.md:1–5` explicitly supersedes its older partial-status narrative. Its old five-contract and 112-module statements are not presented as current results. Likewise, the historical Open label in the frozen canonical snapshot is explicitly identified as historical, not a present openness assertion. Failed logs are retained and not counted as passes merely because Lean printed recovery declarations.

## Independent inspection of the complete local run

The immutable record is `evidence/runs/20260921T000301098707Z/record.json`, SHA256 `abdf520ffbcfc2fe80236e0c303795d97a50e8c11f46a5edbac8a29dba5d7856`. It records the coordinator's actual run from `2026-09-21T00:03:01.098707+00:00` to `2026-09-21T00:18:29.089795+00:00`.

The reviewer independently recomputed every one of its 125 source hashes, every pinned configuration hash, every log hash, and every current compiled-output hash. All 125 exits are zero. The actual 386 axiom reports match Audit's 386 distinct expected names exactly and use only `propext`, `Classical.choice`, and `Quot.sound`. The Audit log SHA256 is `a1e73e7919dc4a8877bf5e2814c9b225c8781739818459a6170f50d7d646d098`. The frozen manuscript hash matches, and `evidence/latest-local.json` is byte-identical to the immutable record. No mismatch was found.

The record explicitly says `comparator: "not_run"` and `github_run_id: null`. This review inspected retained local evidence; it did not independently rerun Lean or any Linux verification. The complete theorem's first individual test finished on 20 September UTC; the subsequent integrated run completed on 21 September UTC. The different dates in VERIFICATION are consistent with those timestamps.

## Reproduction corrections and their limited test scope

The successful full proof run used runner SHA256 `fddada659794fdf62748ffc0790368c30b1bf66ff0acc939161edbd1fd4b8d85`. Before changing that file, the reviewer archived its exact bytes as `evidence/runs/20260921T000301098707Z/verify_local.py`, matching the immutable record's `runner_sha256`.

The current runner, SHA256 `67b74e0aedc0d6896d1ccaf7e57de3e70b156c56e706e77d6c43703a5ef9a128`, retains `/private/tmp/nla-lean-compiler.lock` on macOS and uses Python's system temporary directory on other platforms. The command remains `lake env lean -j1 -M4096 -o ...`, with `LEAN_NUM_THREADS=1`, sequential subprocess waits, and the same nonblocking exclusive lock. No compilation command, source list, permitted axiom set, or proof source was changed. The unqualified `lake build Solution` reproduction shortcut was removed; the documented local procedure uses the serial Python runner.

`evidence/runner-portability-smoke.py`, SHA256 `9568b4563e4ec1b23ce3e395cbe01e9fa2699d8a95a1dbd773c64777e9b33eac`, was actually executed with `python3 evidence/runner-portability-smoke.py`. Its result is retained in `runner-portability-smoke.json`, SHA256 `b9d7f269d82018fcd0567ed760c4561d861464c296129800af72fb96b723cabe`, and its output log has SHA256 `1ec9cf2ce0cb5ac07e06e72ef2e27661702af91a2a737a40f1888cedfa012747`.

That smoke check covers three mocked platform/directory selections, real exclusion of a second Python process while an exclusive `flock` is held, successful acquisition after release, and AST equality of the runner's main function except for lock-path selection. It also confirms no drift in any of the 125 proof-run source hashes. It ran on macOS; the Linux path-selection cases are mocked, not a claimed Linux execution. No Lean or Comparator was launched. Thus the complete Lean run applies to the archived runner, while the portability change has separate Python-only evidence.

## Metadata, source locations, and attribution

The current `evidence/metadata-validation.json` has SHA256 `24ed9b128b26e4805f5630c22f3ac1fa4af82128b8724ea8550e1452adb64910`. It records an actual call to the unchanged upstream `validate_manifest.validate`, with output `Manifest schema and comparator coverage: PASS (7 declarations)`. The validator hash is `31e473132c1e8a40c29f73eff01fbff0bafe85649da601d2f550cef164debeb1`; the official v0.4 schema hash is `25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce`. The reviewer matched both to the local supplied files, matched the metadata and comparator hashes to the record, independently parsed the YAML, and checked exact seven-declaration coverage and self-contained source locations. This is inspection and coverage checking, not a new schema-validation execution by the reviewer, and schema validation is not proof verification.

The mathematical source locations now point to `original-proof/solution.md` and `original-proof/problem.md`, which remain valid when the project is copied under `matrix-functions-and-stability/MF-21/lean-frozen-2026-09-12`. There is no remaining need to rewrite the canonical source path to `../README.md` for this copy. The immutable original manuscript-relative links remain byte-for-byte preserved; `original-proof/README.md` supplies explicit immutable historical review/submission links and distinguishes them from current evidence. Their referenced git blobs exist. The main current documentation links resolve.

The reviewer checked the original manuscript blob at commit `eb37bc17a462177f57efa270e9a9f9b17e9d88e2`: it is exactly SHA256 `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`, 19,864 bytes. The canonical snapshot exactly matches commit `9b35b5e246989843cd67b2fed702216ea1f0acdb` at the documented path and SHA256 `1aac38ed3c7a83dfc3dddb4beeec26fcf117f23f5789b2a374c1332ba4cf359f`.

Separately, a path-inventory and hash-only inspection of publication-base commit `aa8d010bdd5a3ef1750c9fa013b67b6d90786d96` confirmed an existing `MF-21/lean` tree and a different current `MF-21/solution.md`, SHA256 `c62ac12d4982c97cb97d9ee57cd6c20ebc5e4726e6a7cab99379886287fa9e25`, 27,653 bytes. No mathematical text or Lean proof from that other formalization was opened or assessed for this comparison. It establishes only that the additive publication preserves separate upstream work; it does not establish novelty, superiority, or verification of that other work. A second formalization is not a second distinct target.

The attribution and vendor files preserve the cited original mathematics, the external six-file π proof's author/license/port provenance, and Mathlib/LeanCert acknowledgements. A text scan found no contact email in current metadata, attribution, or frozen manuscripts. The sole email-shaped match in the broader retained logs was a Lean-generated hygienic identifier, not a contact address.

## Exact reviewed document versions

| File | SHA256 |
|---|---|
| `README.md` | `9a7d3f138957f0cc193c3b54739694a63293570914c79c3d8ba6d6f34c0d4813` |
| `VERIFICATION.md` | `d7fdf1ddbd351ea0f092a69f8cabeb36c3a572d677b6fc80f5e299723100607a` |
| `STATEMENTS.md` | `dda8ed2a0571b7d48c78ef03d7289aeca57d529b15e42caf5b1404eb32332a2f` |
| `NUMERICAL_TARGETS.md` | `bed5a317615d5fef1a8e94df49352ca7bdf67f8a16c4d0327860270b92728000` |
| `formalization.yaml` | `3448a61dc1a77ea9e13dd672ad4be93544f0aabf5f4123850b7896ec1368e3a3` |
| `VERIFICATION-HISTORY.md` | `2f2e9254d279d1ca715d000a1fb3936b04e188d2f7ccca96e1db39ffe6cd200c` |
| `original-proof/README.md` | `cc93b77b8d4eb20339b745b9d7b0f5d595aa155b889f4f9c837d6fb79649450f` |
| `original-proof/problem-provenance.json` | `fc94294687575bde1a2c4adbd1e0b4cf6e19a6707e4abb676e058d7261bf8960` |
| `vendor/gotrevor-pi/README.md` | `5c7e88613e94c05d9f5e6f0073f8a927d2437dc9d3ec7998f86970f1d317daf7` |

## Linux and publication boundary

The existing pinned harness at publication-base commit `aa8d010...` was inspected as infrastructure, not as a proof of this target. Its source lock pins Lean 4.33.1 and the Forsythe-derived checker files; `harness.py` accepts a self-contained project path, makes a fresh committed-source copy, disallows compiled artifacts and definition holes, and invokes the actual Comparator through the reviewed Landrun/Bubblewrap and restricted user-service mechanism. Source-lock SHA256: `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`; harness SHA256: `f81767a17973956fbe9e5765c664d4639cce15ddf8c106f70cdcb32151808c2f`. No bootstrap, sandbox probe, checker control, or Comparator execution was performed by this reviewer.

The existing generic selector also selects the old MF-21 Lean project for changes anywhere under its canonical problem directory. A brand-new remote branch with an all-zero before-SHA triggers its all-project path. These cost/scope facts were reported to the coordinator, who is planning the separate branch seed and dedicated exact-project workflow. This report does not certify a dedicated workflow that had not yet been supplied for final inspection, nor any future selected-project result. The published commit, actual selected project, seven checked declarations, exit status, run ID, and artifacts remain required evidence for the final GitHub claim. No completed-verification or distinct-problem count is added by this review.
