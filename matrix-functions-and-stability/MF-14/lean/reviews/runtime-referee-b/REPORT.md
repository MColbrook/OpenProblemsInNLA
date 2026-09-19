# MF-14 repaired proof — independent runtime referee B

**Verdict: APPROVE the runtime evidence for repaired proof commit `c89c859a6b21c399a99f5e9f5fb2b7f472c96657`.** Both official GitHub runs passed the actual fresh Comparator/default-kernel/sandbox checks for all 25 MF14 contracts. Their result receipts match all 536 tracked project inputs at that commit. All 87 Lean files also match the repaired frozen packet approved in the separate independent continuation review.

Reviewer: `/root/nr04_mf14_final_referee_b`, independent nonauthor AI agent, 19 September 2026. I retrieved and audited official evidence, not a coordinator's success summary. I authored no MF14 proof or repair, ran no Lean/Lake/Comparator locally, edited no proof/workflow, and performed no remote write, commit, push, publication, promotion or count increment. This report covers the named proof commit; any later publication amendment is a separate provenance question.

## Official runs and artifact authentication

| Scope | Official run | Verify job | Artifact |
|---|---|---|---|
| Fork push | [35433896875](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35433896875) | 105873255308 | 10581683130, `lean-MF-14`, 38,818 bytes |
| Upstream PR 305 | [35433898434](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/35433898434) | 105873251674 | 10582237117, `lean-MF-14`, 39,324 bytes |

The official run records identify the exact repaired head, `.github/workflows/lean-verification.yml`, and completed success. The fork verification job finished at 09:25:14 UTC; the upstream verification job finished at 09:21:30 UTC. Each jobs list and actual selection log contains exactly one selected project: `MF-14`, `matrix-functions-and-stability/MF-14/lean`. The fresh verification and artifact-upload steps succeeded. The optional separate checker-controls job was skipped because shared tooling was unchanged; all mandatory controls ran inside each verify job.

The fork checked the proof commit itself. The upstream checkout and result receipt identify merge commit `84f2d7bd1f2d7613e8e7812f60ece7800dca429d`. I retrieved the official Git object and confirmed its ordered parents are base `71563f17926cd826a892c2bba0e294894ee57a5c` and the exact repaired proof commit. Official verify-job logs independently show these checked commits. The merge SHA is not being conflated with the PR head SHA.

I waited for both completed outcomes before caching official evidence. Fourteen successful read-only GitHub REST requests retrieved run, jobs, artifact and checked-commit objects, both ZIPs, and both selection and verification whole-job logs. `RETRIEVAL-COMMANDS.json` records exact CLI arguments, times, exits, output paths and SHA256 hashes. `RETRIEVAL-INVOCATION.json` records the top-level collection command. The downloaded ZIP hashes and byte lengths match GitHub's metadata:

- Fork ZIP: `552d7e5578d4f582b7e4ed3162249e26d9abda74d9e254df4aed0cf6d279f4d8`.
- Upstream ZIP: `c9fc3f22572e78fc827f44202348e9e3cf156f087950dc1658a04b5335110d2f`.

Each ZIP contains 13 ordinary files. Safe extraction rejects absolute/traversal paths, symlinks, special files and duplicate normalized names, bounds the expanded size, and confines writes to the new local evidence directory. `ARTIFACT-FILES.json` records every extracted hash. Raw whole-job logs were saved using the CLI's explicit terminal-escape opt-in; their content was read as data, not executed.

## Exact source, contract and tool binding

The strict audit independently hashes the 536 Git blobs under the project at the repaired proof commit and compares the complete map with each receipt's `input_sha256`: no missing, extra or differing entry. This binds sources, Challenge, configuration, dependency pins and published metadata to the actual accepted input. Separate checking binds all 87 Lean hashes to `MF14-v2-instance-alignment`, snapshot SHA256 `10b1b576719a24d12d3a123a1180c2c89d26626a41367ef0abaf42001cb52892`.

The published and recorded Comparator configs agree exactly: separate `Challenge` and `Solution` modules, 25 unique named theorem contracts, no replaceable definitions, and permitted axioms limited to `propext`, `Classical.choice`, `Quot.sound`. Both export records contain all 25 contracts. Each actual `Solution.lean` build emits all 25 corresponding axiom reports with only those three standard axioms. The actual target comparator logs then say:

```text
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
EXIT_STATUS=0
```

These are the MF14 proof's own final markers, not acceptance text borrowed from a positive control. The previously failing `integer_jacobian_mod3_inverse` is among the accepted exports and actual axiom reports. The scoped instance-selection repair therefore has actual Comparator/kernel evidence in addition to the separately authenticated local raw-expression comparison.

The shared harness, `tools/lean`, `docs/lean` and workflow are unchanged from the published base. I inspected their source-only snapshot, ordinary-file restrictions, clean environment, source/pin checks, unchanged-input checks before and after cache preparation and Comparator, and control ordering. No prior Solution build is used in the fresh project; dependency/cache preparation precedes Comparator's own Challenge/Solution builds. Immutable copies of the relevant proof-commit verifier and project config blobs are in `reviewed-verifier-inputs`.

Both tool/result receipts match source-lock SHA256 `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`, covering 58 pinned files at Forsythe commit `8d1b0c0545a77b40245e84705aa7d273e6c81e62`. Receipts record and the unchanged harness rechecks the real Comparator, lean4export and Landrun executable hashes. Both runs use Lean 4.33.1, x86_64 Linux, and Go 1.27.1; the recorded platform is Linux 6.17.0-1022-azure. All ten actual dependency checkout log entries match the published Lake manifest, including LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

I rehashed the five archived strict-adapter/control sources against the lock and rechecked the exact text-only CI sandbox-probe adaptation. Its computed SHA256 `31057195baf238807cacbb4126c5b07f02cec55a4e4437de5f3a755b3fada803` matches both receipts. This is an independent provenance/log audit of the pinned checker, not a new checker rebuild or a new local Comparator run.

## Actual controls and unprivileged execution

Both authenticated artifacts pass the user-service probe with `systemd-run --user`, AF_UNIX restrictions and `/run/user/1001`. Both build and export sandbox probes explicitly report UID 1001. The detailed audit checks every expected result:

- Outside-directory writes, creation, truncation and symlink escapes are denied; the designated build `.lake` write succeeds, while export writes/truncation are denied and outer/export fixtures remain unchanged.
- User/PID/mount/network/IPC/UTS namespaces are private; host parent process access and signaling fail; host loopback and AF_UNIX sockets are unavailable; capabilities are empty, `no_new_privs` is set, and a nested namespace write is rejected.
- Unknown wrapper options and the three arbitrary/relative write-option cases each fail with exit 2.
- The real `Comparator.runBuiltinKernel` accepts the honest inductive/quotient fixture, rejects an invalid raw proof through the kernel type check, and rejects forged quotient data through the post-check.
- All five Comparator regression cases produce their required results, including actual type mismatch rejection.
- Fresh `sorry` and `native_decide` controls fail with exit 1 for `sorryAx` and `checked._native.native_decide.ax_1_1`, respectively.

Only after these controls do the actual MF14 logs establish complete target acceptance. The retained artifact commands expose the real strict wrapper and pinned tools; no permissive fallback or substitute checker appears.

## Records, prior failure and privacy

New evidence directory: `.local-recovery-20260918/verification/MF14-repaired-linux-20260919`.

- `INDEPENDENT-AUDIT.json`: `a70c8938f3f0431b2a9adbb4d2c3a03701e7bd1a7666942c4446357d3140ea30`.
- `INDEPENDENT-DETAILS.json`: `e199f80b76f4b68aa33d6f4cf3d56d8152ec8fb84467353a83872a78f37ad8bd`.
- Fork successful result receipt: `292bd89f5ac21d86eb4535365038aff8a2bbd15ad6315051fc6ba699514e3474`.
- Upstream successful result receipt: `92a7b40dfe5f0682ba553b0666210f974053e6190671dc8a13d9efac72197c71`.

`AUDIT-COMMANDS.json` records the two successful read-only audit invocations. The accompanying `MANIFEST.json` binds this report, exact scripts, source/continuation reviews and all official evidence. The strict success auditor was used unchanged. The extra details checker was adapted only to the MF14 project and repaired snapshot.

The old failed evidence at `verification/MF14-linux-20260919` and blocking report at `reviews/MF14-runtime-referee-b` remain historical records. I rechecked the failed-report manifest and all 81 failed evidence files unchanged. This new approval covers a new commit and new real runs; it does not relabel the old failures.

Raw official metadata contains personal contact information and is retained locally only. I copied no raw metadata or artifact into the public worktree. Any coordinator-published derivative must retain an explicit original/sanitized hash mapping; this audit authenticates the original local bytes. The report itself publishes no personal email address.

No blocking runtime-evidence issue remains for this exact repaired proof commit. Mathematical fidelity is covered by the separate full v1 review and exact v2 continuation, whose scope is the original equality-42 refutation via universal degree-44 full-coefficient coverage, not an exact degree-47 claim. Coordinator integration and any later metadata-head checks remain separate from this runtime approval. No count or canonical status was changed by this referee.
