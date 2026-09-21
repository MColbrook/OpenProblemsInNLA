# Independent publication-workflow review

Verdict: **APPROVE for the static workflow and unchanged-harness scope described here.** No material workflow issue was found. This report is not a successful CI, Comparator, sandbox, kernel replay, or final publication audit. I ran no Lean compiler and edited no workflow, proof, or shared harness source.

## Exact reviewed inputs and scope

The new workflow is `/private/tmp/nla-mf21-frozen-publish-20260920/.github/workflows/mf21-frozen-verification.yml`, SHA-256 `eb8a5aecaefab354c61825e5bd3ad1d31b53a7ca880192756581529e8b299012`. The publication checkout's inspected base HEAD is `aa8d010bdd5a3ef1750c9fa013b67b6d90786d96`. At inspection, this workflow was untracked and the new proof project had not yet been populated in this sparse checkout. Consequently this report approves the workflow logic, not a final committed proof-package snapshot or its still-to-be-written metadata.

I read the workflow, `bootstrap.sh`, `verify.sh`, the complete `harness.py`, `validate_manifest.py`, `projects.py`, the existing generic workflow, harness/provenance documentation, and the relevant schema. I recomputed the workflow hash and byte-compared all 17 checked files under `tools/lean`, `docs/lean/schema`, and the existing generic workflow against their blobs at the base HEAD. All matched exactly. No shared harness or generic selection change accompanies this workflow.

This applies the Comparator/trust-boundary and source-fidelity portions of the pinned referee standards, SHA-256 `e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`. It is not a new audit of the fetched Comparator implementation or of the separate existing upstream MF-21 proof.

## Project selection and additive publication

The dedicated job has the literal project path

    matrix-functions-and-stability/MF-21/lean-frozen-2026-09-12

at workflow line 30. That same variable is passed to both metadata validation and `verify.sh`; the job has no project matrix or automatic all-project discovery. Push and pull-request filters cover only this new project, this workflow, shared Lean tools, and the schema. The explicit manual trigger still runs only this fixed project. Sparse checkout includes the required workflow/tools/schema paths and the complete new project.

The base Git tree already contains the separate canonical `matrix-functions-and-stability/MF-21/lean` project. Its existing `solution.md` blob has SHA-256 `c62ac12d4982c97cb97d9ee57cd6c20ebc5e4726e6a7cab99379886287fa9e25`, different from the frozen manuscript's `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`. The new workflow selects the additional directory, so it does not substitute the old project's proof or verification evidence. The final publication diff must preserve the existing project and original IDs. This is another formalization of the same canonical MF-21 target, not a second completed distinct target to add to a count.

I evaluated the unchanged pure project-selection function against the actual base registry/tree, containing 60 existing projects, and the planned new-project/workflow paths. It selected exactly the existing `matrix-functions-and-stability/MF-21/lean` project. This is expected: the generic workflow selects a registered project's entire problem parent when that parent changes. Its eventual result must be distinguished from the dedicated frozen-manuscript result. The generic selector does not discover `lean-frozen-2026-09-12` by itself.

The proposed branch-seed commit marked `[skip ci]` is an operational plan, not an executed check in this review. To avoid a new-branch push with a zero `before` SHA invoking the generic select-all branch, that seed must actually be pushed separately before the proof commit. The later proof commit must trigger the checks normally. The generic workflow's explicit all-project selection on a manual dispatch or zero-base event remains unchanged.

## Metadata and fresh-source verification

The workflow runs `validate_manifest.py` on the exact fixed project before installing the checker tooling. The unchanged validator enforces the pinned v0.4 schema, rejects duplicate YAML/JSON keys, requires a nonempty distinct Comparator target list, rejects definition holes and nonstandard permitted axioms, requires zero reported proof-development sorries, and requires every advertised result to occur exactly once in `comparator.json` with an existing project-local source path. These are consistency gates; they do not establish that a claimed review occurred or that a theorem is true.

The Lean action has `auto-config`, `build`, `test`, `lint`, Mathlib cache use, and GitHub cache use all explicitly disabled. The workflow adds no separate `lake build Solution` or precompilation of candidate proof modules. Bootstrap builds the pinned checker/exporter/Landrun tools in the runner-temporary tool directory, not the candidate proof.

The unchanged harness then checks the tools and runs all controls before handling the candidate. `snapshot` at `harness.py:317` checks for tracked changes, resolves the actual repository HEAD, and copies ordinary tracked blobs from that commit into a new temporary project directory. It rejects symlinks, submodules, tracked `.lake` contents, and compiled artifacts. It records each copied file's SHA-256. Untracked local build outputs are not trusted proof inputs.

`validate_project` requires the TOML Lakefile, contained package directory, immutable HTTPS GitHub dependency revisions, distinct valid Challenge/Solution modules, a nonempty distinct target list, no definition holes, and only standard permitted axioms. The toolchain must exactly equal the pinned Lean 4.33.1. Dependency materialization and the trusted Mathlib cache occur before Comparator, with committed-input hash checks after each preparation step. There is no candidate Solution build in that fresh directory before Comparator. The final Comparator invocation is followed by another committed-input hash check.

The final project must therefore be self-contained inside the selected directory, with every required original-proof artifact committed inside its copied layout. A parent-directory file that happens to exist in checkout is not copied by this snapshot routine. This condition is to be checked when the publication project is populated; this report does not assert that packaging check has already happened.

## Isolation, controls, and failure handling

The job uses `ubuntu-24.04`; the workflow prepares Bubblewrap and a user systemd session with privilege only for host preparation. The verifier itself is invoked without `sudo`. `linux_requirements` rejects non-Linux execution and UID 0, and requires Bubblewrap, systemd-run, and timeout. No fake sandbox fallback is selected.

The tool lock fetches 58 files from immutable Forsythe commit `8d1b0c0545a77b40245e84705aa7d273e6c81e62`, checking each byte count and digest. Bootstrap records tool binaries and the derived noninteractive probe. Verification rechecks the locked sources, tool binaries, environment file, probe derivation, and exact Lean version. The existing probe derivation retains both `RestrictAddressFamilies=~AF_UNIX` restrictions and all isolation assertions; it changes transport/deadlines and a probe-only executable allowance documented by the unchanged harness.

Before candidate verification, `run_controls` invokes the real user-service startup check, sandbox probe, three kernel replay controls, five Comparator controls, and the additional rejection fixtures for `sorryAx` and native-execution trust. Negative fixtures require both the expected rejection exit code and their specific diagnostic markers. They are checker tests, not mathematical results.

The actual Comparator process is launched with `systemd-run --user --wait --pipe --collect` and `RestrictAddressFamilies=~AF_UNIX`; its tool environment selects the pinned strict Landrun/Bubblewrap adapter. `--wait --pipe` propagates the service outcome. The harness's `logged` function rejects unexpected status or missing required success markers. Its main entry point returns a nonzero status on a failed precondition/check. The shell wrappers use `set -euo pipefail`, and the workflow supplies no `continue-on-error`, success-forcing fallback, or ignored verifier status.

The workflow's 90-minute deadline, tool/package availability, runner namespace policy, available memory, and systemd session are real runtime conditions. This static review does not establish that they will suffice. Failure or timeout remains a failed/incomplete run and must not be labelled verified.

## Source-commit evidence and artifacts

The job uses read-only repository permissions, immutable action commit pins, and checkout with `persist-credentials: false`. The final artifact step runs with `if: always()` and uploads the dedicated tool directory's complete `logs/` subtree under `mf21-frozen-${{ github.sha }}`. A missing-log warning does not neutralize a previous job failure.

On success, `verify` writes a fresh `result.json` containing the actual checked repository commit, exact project path, selected Comparator configuration, hashes of every committed input, checker source-lock hash, and tool receipt. The retained Comparator log must contain both kernel acceptance and final statement/axiom acceptance markers. These fresh records, together with the GitHub run identity, are the evidence to retain and report.

For a pull-request event, checkout and `github.sha` may identify GitHub's merge commit rather than the branch head. The `repository_commit` in the verifier receipt is authoritative for what was actually checked; it must not be silently relabelled as the branch-head commit. The artifact label alone is not a verification verdict. Cancelled, failed, or superseded runs remain distinguishable from a final successful run. Bootstrap's full receipt is embedded in the successful verification result; early failures may retain only the logs available at that point.

## Hashes and checks actually performed

| Reviewed file | SHA-256 |
|---|---|
| New dedicated workflow | `eb8a5aecaefab354c61825e5bd3ad1d31b53a7ca880192756581529e8b299012` |
| Existing generic workflow | `2c3963089483ec5e7e35e6355fa60988778e0b439ce099d7cd7050a8c3b6467c` |
| `tools/lean/harness.py` | `f81767a17973956fbe9e5765c664d4639cce15ddf8c106f70cdcb32151808c2f` |
| `tools/lean/bootstrap.sh` | `4cb4d6e09ca5d186e1911e51160286fef20fb4d7f61180e07ed684a03d36de8c` |
| `tools/lean/verify.sh` | `fb97ffb467b0e9acac302b2bdfc418da12b88e4ae307fb0d580c96fd6b63e997` |
| `tools/lean/source-lock.json` | `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b` |
| `tools/lean/validate_manifest.py` | `31e473132c1e8a40c29f73eff01fbff0bafe85649da601d2f550cef164debeb1` |
| `tools/lean/projects.py` | `dbb8e2df074d2518c4457ff66229891161104767381762fbd5f96d7f28dee149` |
| `docs/lean/schema/v0.4.schema.json` | `25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce` |

Actual local review checks were source reading, SHA-256 computation, comparison with base Git blobs, Python AST parsing of the three driver/validator/selector files, and execution of the pure project-selection function on the stated paths. PyYAML was unavailable in the referee's Python environment, so no YAML parser validation is claimed. No packages were installed. The existing project's metadata blobs were not locally available in the partial clone; attempts to read them required an unavailable network fetch, and their contents are outside this report's reviewed scope.

I did not run the workflow, bootstrap, verifier, metadata validator on a populated publication project, Lean, Comparator, or any sandbox/kernel control. Final packaging checks and the real GitHub run remain necessary and must be recorded separately.
