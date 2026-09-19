# MF-14 independent runtime referee B — failed proof commit

**Verdict: BLOCKING. Both official runs rejected the elaborated statement of `NLA.MF14Degree44.integer_jacobian_mod3_inverse`.** This report covers proof commit `fe4bbee26cc79f06587c803c5c902164c1e02e8e` only. The Challenge and Solution Lean builds succeeded, but Comparator exited 1 before starting default-kernel replay of the actual MF14 solution. The verification step exited 2. Neither artifact contains a successful `result.json` receipt. These runs do not establish completed Linux verification and must not support promotion or a completion count.

Reviewer: `/root/nr04_mf14_final_referee_b`, an independent nonauthor AI agent, 19 September 2026. I retrieved and inspected actual official evidence and ran only read-only Python/hash/Git audits. I ran no Lean, Lake or Comparator, authored no repair or proof, changed no workflow, and performed no publication, commit, push, rerun or count increment. Root's later local diagnosis and proposed repair are outside this failed-commit report.

## Official provenance and exact failure

| Scope | Official run | Verify job | Artifact |
|---|---|---|---|
| Fork push | [35431937168](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35431937168) | 105868030877 | 10581150411, 18,769 bytes |
| Upstream PR 305 | [35431941636](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/35431941636) | 105868048984 | 10580509887, 19,652 bytes |

Both official run records say `completed` / `failure` for the exact proof head and `.github/workflows/lean-verification.yml`. Each jobs list and selection-job log selected only `MF-14`, `matrix-functions-and-stability/MF-14/lean`. The failing step is number 7, `Fresh sandboxed statement, axiom and kernel verification`. The separate optional checker-controls job was skipped; the mandatory control phases did run inside each verification job.

Both actual `comparator.log` files show successful Challenge (2138 jobs) and Solution (3723 jobs) builds, exports from each environment containing all 25 contracts, and all 25 actual `Solution.lean` aggregate axiom reports. The reported axioms are confined to `propext`, `Classical.choice`, and `Quot.sound`. The next outcome is identical in both logs:

```text
uncaught exception: Challenge and solution theorem statement do not match: 'NLA.MF14Degree44.integer_jacobian_mod3_inverse'
EXIT_STATUS=1
```

The actual MF14 comparator logs contain neither the start of solution default-kernel replay, solution-kernel acceptance, nor `Your solution is okay!`. Acceptance text in the whole-job log belongs to the separate control fixtures; it cannot be used as acceptance of MF14.

The failing implementation declaration is at `NLA/MF14Degree44/Mod3Certificate.lean:140`; the frozen reference is at `Challenge.lean:142`. Their literal source headers are identical:

```lean
∃ B : Matrix (Fin 45) (Fin 45) (ZMod 3), integerJacobianMod3 * B = 1
```

Literal source equality did not suffice for Comparator's elaborated-statement comparison. The official logs name the mismatch but do not print the elaborated expression difference. This report therefore does not attribute a more specific cause. The prior mathematical/source approval does not override this concrete runtime blocker.

## Artifact authentication and source binding

I retrieved official run, jobs, artifact and checked-commit REST responses, both ZIPs, and both selection and verification whole-job logs. Exact CLI arguments, retrieval times, exit codes, output paths and hashes are in `RETRIEVAL-COMMANDS.json`. ZIP byte lengths and SHA256 digests match the official metadata:

- Fork: `1a3becd36dd4e17c94bedbc2aac20583a683b598aafa69be84fdeb48691dfd9a`.
- Upstream: `6cf2591d87b66a17fb98d884496c11616758e4ec93303ee06927f6f35b4c74da`.

Each ZIP contains 12 ordinary files. Extraction rejects absolute/traversal paths, symlinks, special files and duplicate normalized names, bounds total extracted bytes, and confines writes to the evidence folder. `ARTIFACT-FILES.json` retains every extracted hash.

The fork checkout log identifies the proof commit itself. The upstream checkout log identifies `512392344c6c47a0feddd3fb8c6d0b6233a68367`. Its retrieved official Git object has ordered parents `71563f17926cd826a892c2bba0e294894ee57a5c` and the proof commit. Both checked commit objects identify the same complete Git tree as the proof commit. This uses the actual checkout log, not an assumed PR merge SHA.

I independently hashed all 274 tracked project blobs at that immutable proof commit. All 87 Lean hashes match the frozen MF14-v1 snapshot `e52fab5a7b58c3bc6fb2c2df1283d55c6e4352056689c900de936c12e2595436`. The published configuration names exactly 25 unique theorems, separate `Challenge` and `Solution` modules, no replaceable definitions, and only the three standard permitted axioms. Relevant proof/configuration/harness Git blobs are preserved under `reviewed-proof-inputs`; the complete input map is `PROOF-INPUT-HASHES.json`.

Unlike a successful run, these failed archives do not preserve a result receipt, bootstrap receipt, or runtime input/executable hash map. I consequently do not claim to have compared such maps. Source binding rests on the authenticated checkout/tree and the unchanged harness: it copies only ordinary tracked Git blobs into a fresh project, rejects tracked build outputs, and checks inputs unchanged after dependency/cache preparation. The failure interrupts the final post-Comparator unchanged-input check and successful receipt emission. This limitation is explicit in `INDEPENDENT-AUDIT.json`.

## Compiler, options, environment and controls

The official logs identify Ubuntu 24.04.5, runner image `ubuntu-24.04`, Lean 4.33.1 on `x86_64-unknown-linux-gnu`, and Go 1.27.1 on Linux/amd64. The pinned Lake manifest's ten dependency revisions match the actual checkout log, including LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Dependency setup and source-matched Mathlib cache preparation exit 0 before Comparator's builds.

The exact remote command is preserved as the first line of each artifact log. The proof command invokes `lake env .../comparator comparator.json` through `systemd-run --user`, a clean `env -i`, `RestrictAddressFamilies=~AF_UNIX`, and the real strict sandbox wrapper. The workflow sets `ulimit -n 65536`. The project Lake file selects `Solution`, imports LeanCert at its pin, and supplies no extra Lean build-option list. The failing module sets `autoImplicit false` and `leancert.trust "kernel"`; its declaration has no local resource option. No claim is made that local one-thread/4096 MiB development limits were remote command-line options.

Shared verifier, documentation and workflow sources are unchanged from the base. The source-lock SHA256 is `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`, pinning 58 tool sources at Forsythe commit `8d1b0c0545a77b40245e84705aa7d273e6c81e62`. I rehashed the five archived strict-adapter/control sources against that lock. The unchanged harness enforces the whole lock and tool integrity as preconditions; actual executable hashes are unavailable in these failed artifacts.

Both authenticated runs provide successful user-service, build/export sandbox, actual kernel-control and five-case Comparator-regression logs. Both sandbox modes explicitly report UID 1001. Writes/truncation/creation outside the allowed build directory, symlink escapes, export writes, host process/network access, AF_UNIX creation, effective capabilities and nested namespace writes are denied; private namespaces and `no_new_privs` are checked. Four malformed wrapper-option cases exit 2. The real kernel-control accepts the honest inductive/quotient fixture, rejects a raw invalid proof by kernel type checking, and rejects forged quotient data. The fresh `sorry` and `native_decide` controls each exit 1 for their forbidden axiom. The detailed audit checks every marker and expected exit separately. Successful controls do not cure the actual MF14 statement rejection.

## Preserved audit and scope

Evidence: `.local-recovery-20260918/verification/MF14-linux-20260919`.

`INDEPENDENT-AUDIT.json` SHA256 is `0e04a6283ccbd67c283d0d7b60c55b1e86482d18a57ebc5ea0a6aec4ddf075e8`. Its verdict records the blocker, not a runtime PASS. `MANIFEST.json` beside this report binds the report, auditor/collector, raw official evidence, selected immutable source blobs and the earlier mathematical review.

The collector gained one explicit failed-run path because it previously required a successful `result.json`. This path requires a completed failure and no success receipt, retrieves the official checkout SHA, and authenticates its Git object. The strict success auditor was not relaxed. Two preliminary read-only audit attempts encountered a missing local archived-source path; their errors remain in `AUDIT.stderr` and `AUDIT-2.stderr`. I corrected the local archive lookup to the five actually available control sources, then completed the audit. No runtime failure or missing receipt was converted into success.

Any repair must receive its own source/evidence review and actual successful GitHub checks. This directory remains the permanent record of the two failed runs; later repaired evidence belongs in a new directory.
