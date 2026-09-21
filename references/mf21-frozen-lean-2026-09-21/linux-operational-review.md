Verdict: **APPROVE the authenticated Linux Comparator, default-kernel, standard-axiom and sandbox verification for commit `fe2183e9b570322d7c1f64bba3480460082af8d3`.** This is an executed target acceptance, not a pending run or a checker-fixture result.

This bounded independent review was completed on 2026-09-21 UTC by the proof/evidence referee, who did not author the proof, memory repairs, workflow or harness. I read the dedicated workflow, harness, source lock and Comparator configuration, checked publication binding, and independently authenticated and inspected the completed runtime evidence. I ran no Lean compiler, dispatched no workflow and changed no proof or verification source. This is an operational review; the separate statement, proof-assembly and local-evidence reviews retain their stated scopes.

Using `/private/tmp/mf21-verifier-tools/gh api`, I independently queried the run, jobs and artifacts endpoints for `sgstepaniants/OpenProblemsInNLA/actions/runs/35552653565`. GitHub reported a completed successful push run of `.github/workflows/mf21-frozen-verification.yml`, attempt 1, on the exact commit above. Its sole job, `verify-frozen-manuscript` (job `106190154763`, `ubuntu-24.04`), and the actual verification step succeeded; the job completed at `2026-09-21T02:08:57Z`. [Authenticated run](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35552653565).

GitHub listed one unexpired artifact, `10619061816`, named `mf21-frozen-fe2183e9b570322d7c1f64bba3480460082af8d3`, explicitly associated with this run and head commit. I independently downloaded its ZIP through the artifact API. Its 64,859 bytes have SHA-256 `c6d51651303f5c4b5d7910e7b84f85b38c26a9ae9719efd9539ab321f7c06a94`, exactly the API digest. All 13 file names and byte hashes matched both the retained [artifact directory](linux-attempt-03/) and [download receipt](linux-attempt-03.json); there were no duplicate ZIP file paths.

I enumerated the immutable Git tree at the verified commit and read its blobs with `git cat-file --batch`. All **1,423** project files, including the complete inventory, matched the actual result's `input_sha256` map and the current publication files under `matrix-functions-and-stability/MF-21/lean-frozen-2026-09-12`. The result's `repository_commit`, project path, source-lock hash and complete configuration matched these Git objects. The current worktree HEAD was `0d314d9957d9a7b68ac4af125ed7e527a4683e52`; this report claims the run at `fe2183e9…` and separately confirms identical project bytes at the time of review. The previously checked publication receipt and local phase-recheck record therefore bind to the same project accepted on Linux.

The workflow, harness and source lock are byte-identical to their previously reviewed versions at `bd3014e699f277500beabda57cfeb1f57925ab78`. The dedicated workflow selects only this project, disables the Lean action's automatic build/cache/test/lint operations, bootstraps the real tools and calls verification without ignoring failures. The harness rejects root and non-Linux execution. It verifies 58 locked source files from Forsythe commit `8d1b0c0545a77b40245e84705aa7d273e6c81e62`, validates its built-tool receipt and uses Lean `4.33.1`. Its reviewed CI probe adaptation preserves the isolation assertions. The retained tool receipt records the executable hashes; I did not independently rehash Linux executables that are absent from the downloaded artifact.

The harness constructs a fresh snapshot from committed ordinary files, rejects tracked build artifacts, permits no definition holes, restricts axioms to `propext`, `Quot.sound` and `Classical.choice`, and checks source hashes after dependency preparation, cache retrieval and Comparator execution. Before Comparator, project preparation runs only `lake env true` and `lake exe cache get`; the actual logs show pinned dependency checkouts and cache preparation, with no Solution prebuild. The target command invokes the real Comparator through `systemd-run --user`, `RestrictAddressFamilies=~AF_UNIX` and the strict sandbox. Receipt creation requires exit zero and both target acceptance messages. No weakened check or substituted checker was found in this bounded review.

The actual [target result](linux-attempt-03/verify-20260921T020023Z-4146/result.json) says `comparator-accepted`. In the [target log](linux-attempt-03/verify-20260921T020023Z-4146/comparator.log), the Challenge and Solution export lists each contain exactly the configured seven names under `MF21Restart.Contracts`:

- `complex_fourier_eq_cosine`
- `bulk_cutoff_pos`
- `critical_bound_implies_fixed_index_limit`
- `exists_log_sq_bulk_scale_gain`
- `phase_window_margin`
- `manuscript_smooth_target`
- `target_proved`

Comparator builds Challenge and then Solution; the seven expected placeholder warnings occur only in Challenge. The previously problematic `Numerics` and `PhaseWindowRoots` modules build successfully. The Solution export is followed, in order, by `Running Lean default kernel on solution.`, `Lean default kernel accepts the solution`, `Your solution is okay!` and `EXIT_STATUS=0` (log lines 941–945). All 383 printed axiom reports in this target log contain only permitted standard axioms. This count is distinct from the 386 reports in the separately reviewed local Audit runs.

I inspected the actual control logs, including their terminal statuses:

- [Kernel controls](linux-attempt-03/verify-20260921T020023Z-4146/kernel-controls.log): honest inductive/quotient replay accepted; a raw `True` proof presented as `False` rejected by the default kernel; quotient post-check mismatch rejected. All three required outcomes occurred, overall exit 0.
- [Comparator regressions](linux-attempt-03/verify-20260921T020023Z-4146/comparator-controls.log): all five expected outcomes occurred, overall exit 0. The fixture named `simple_kind_mismatch` actually rejects an illegal `helper` axiom; I do not misreport its rejection mechanism. The separate [sorry](linux-attempt-03/verify-20260921T020023Z-4146/negative-sorry.log) and [native](linux-attempt-03/verify-20260921T020023Z-4146/negative-native.log) fixtures each exit 1 as required, rejecting `sorryAx` and `checked._native.native_decide.ax_1_1` respectively.
- [Sandbox controls](linux-attempt-03/verify-20260921T020023Z-4146/sandbox.log): build and export probes run as UID 1001; outside-tree writes/truncation/symlink escapes are denied; only build-mode `.lake` writes are allowed. Private namespaces, inaccessible host process/network endpoints, denied AF_UNIX socket creation, no effective capabilities, `no_new_privs` and rejected nested-namespace writes are recorded. Four invalid permission/option cases each exit 2 as expected, fixture contents remain appropriately unchanged, and the overall probe exits 0. The separate user-service startup check also exits 0.

The principal SHA-256 bindings are:

| File | SHA-256 |
| --- | --- |
| `.github/workflows/mf21-frozen-verification.yml` | `eb8a5aecaefab354c61825e5bd3ad1d31b53a7ca880192756581529e8b299012` |
| `tools/lean/harness.py` | `f81767a17973956fbe9e5765c664d4639cce15ddf8c106f70cdcb32151808c2f` |
| `tools/lean/source-lock.json` | `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b` |
| Project `comparator.json` | `dabddad03ffd9e58d22f1712583ee686d166ede59ebe073798fddd57a928c3ab` |
| `linux-attempt-03.json` | `8fee80805daea6d4b112d82cb6438207f09a5d2d77ad97d81299d596c6224b13` |
| Actual `result.json` | `8fcd531b7e80c5eeda580f7e93a8bc7f7f32b40830ef5405b1f134430db4ee2f` |
| Actual target `comparator.log` | `b84c7bbd7be8929e3079200c0b27b9dd7997c25fd4b655dd191ba152e02a268b` |

No operational blocker remains in this scope. This acceptance does not turn seven exported contracts into seven distinct original problem resolutions, replace semantic refereeing, or retroactively make the two earlier failed Linux attempts successful. The accepted project uses the reviewed 6144 MiB library build ceilings; the separately recorded local verification used its explicit 4096 MiB, single-thread commands. This report makes no claim about measured peak memory or an additional compiler run by the referee.
