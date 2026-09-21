# MF-21 repaired-package evidence review

**Verdict: APPROVE for the current local evidence and its documented scope.** The repaired 125-source package is matched to a completed successful local Lean run and the actual 386-entry axiom log. The reviewed documentation distinguishes that result from the failed first Linux attempt. No successful repaired-source Linux Comparator, kernel replay, or sandbox execution is asserted by this report.

**Reviewer and scope.** Codex agent `/root/mf21_final_statement_referee`, 21 September 2026 UTC. I did not author the Lean proof, numerical repair, compiler runner, or verification records. I previously reviewed the frozen target's statement fidelity; this follow-up independently checks the completed repaired package's retained evidence and the accuracy of `formalization.yaml`, `NUMERICAL_TARGETS.md`, and the final `VERIFICATION.md` snapshot. I wrote only this new report, did not edit older reports or proof/configuration files, and invoked no Lean compiler, Lake build, GitHub command, or network query. Reading another referee's scope for accurate attribution is not a fresh review of that referee's mathematics. The applicable standards remain `reviews/REFEREE_STANDARDS.md`.

**Completed run inspected.** `evidence/runs/20260921T005811719722Z/record.json` records the interval `2026-09-21T00:58:11.719722+00:00` through `2026-09-21T01:13:32.503384+00:00`, `passed: true`, one thread, and a 4096 MiB Lean limit. Its SHA256 is `497c98bffe6628a5adef5653adfb73cf25e04fd27f7306176aea9e34260842c5`. `evidence/latest-local.json` is byte-identical. I inspected the actual files and logs; I did not accept the record's success flag or the coordinator's integrity receipt as sufficient evidence by themselves.

The independent read-only audit found:

- **125 of 125 source hashes match.** The record's source set equals all root `.lean` files and all `.lean` files under `MF21Restart/` and `LeanFormalizations/`. I parsed the runner's `MODULES` assignment with Python `ast.literal_eval`, without executing the runner, and checked that its 125 unique modules equal that actual file set. The recorded invocation order equals that module list. All six vendored transcendence modules, complete-target assembly, project root, wrappers, and Audit are included.
- **Three of three configuration hashes match:** `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`. The runner and frozen manuscript hashes also match. The runner and Lakefile archived beside the new record are byte-matched by SHA256 to the current files. The manuscript remains `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`.
- **125 of 125 commands, environments, and exit codes match the stated limits.** Each command is `lake env lean -j1 -M4096 -o .lake/build/lib/lean/<module>.olean <source>.lean`, with `LEAN_NUM_THREADS=1`, and each returned zero. These are the recorded coordinator executions, not 125 new executions by this referee. The read runner uses blocking `subprocess.run` under the shared compiler lock, serializing its invocations.
- **125 of 125 retained log hashes match**, and **125 of 125 current compiled-output hashes match** the corresponding record entries. The `.olean` output paths were reconstructed from each source and compared with the command arguments, rather than inferred solely from an arbitrary recorded path.
- **All ten package pins match.** For each manifest dependency I independently ran read-only `git rev-parse HEAD` and `git status --porcelain --untracked-files=no` with optional Git locks disabled. Every checkout HEAD equals both the manifest revision and the recorded package HEAD, with no tracked edits. These include Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`.
- **All 386 actual axiom reports match.** I parsed `Audit.log` directly, including multiline axiom lists, and independently extracted the 386 unique `#print axioms` names from `Audit.lean`. Exact name multisets match, with no omission or duplicate. Every parsed axiom set equals the corresponding record entry and is a subset of `{propext, Classical.choice, Quot.sound}`; the union is exactly those three. The actual Audit log contains no `sorryAx`. The main assembly, smooth theorem, canonical theorem, and full-target contract reports are present. `Audit.log` has SHA256 `a1e73e7919dc4a8877bf5e2814c9b225c8781739818459a6170f50d7d646d098`.

There were no source, pin, command, environment, exit-code, log, output, dependency-HEAD, or actual-axiom mismatches. The current 125-source aggregate is `0dc27e2cca2a98b89580bddfc6f6ad8e3a06e0524c690a4886e9c89030bdc023`. Its exact recipe is to sort POSIX relative-path strings, concatenate the UTF-8 lines `<file SHA256><two spaces><relative path><LF>`, and hash that concatenation. Individual per-source hashes remain in the checked run record.

**Historical, isolated, and complete execution evidence remain distinct.** I also checked the older record `evidence/runs/20260921T000301098707Z/record.json`, SHA256 `abdf520ffbcfc2fe80236e0c303795d97a50e8c11f46a5edbac8a29dba5d7856`: its 125 recorded exit codes are zero and all 125 retained log hashes match. Its source map differs from the current package only at `MF21Restart/Numerics.lean`; its configuration map differs only at `lakefile.toml`. The archived old Numerics and Lakefile have exactly the old recorded hashes. That historical run is correctly described as a pass of the earlier version, not of the repaired pair. I did not try to pass off overwritten current `.olean` files as the historical outputs.

The isolated candidate record `evidence/logs/numerics-minimal-candidate-02.json` has SHA256 `80cf97c5c8d989c454d98f2970e0c7a77fa0f2ecccf9e5d7dc58c4d77e38f987`. It records a zero exit from the one-thread, 4096 MiB local command with `-R /private/tmp`, `.olean`/`.ilean`/C emission and JSON diagnostics. Its source hash equals current Numerics, `c4677460fab467e2992c9fd0b1d74abf0d682ba8a7c89857d77e2b481a89e410`; the temporary candidate source is byte-identical to that current source. I rehashed its actual log and parsed its JSON message: the `phase_window_margin` axiom report contains only the three permitted axioms. The candidate log SHA256 is `cf12e33044415f5b0f465b37eda09124ec5693822d32ad0bb328bce7241777be`. This is a real isolated local result. The later 125-source run is the separate complete local integration result.

**First Linux attempt remains a failure.** I inspected the retained local receipt and decisive build-log portions under the publication worktree's `references/mf21-frozen-lean-2026-09-21/`. The receipt identifies GitHub run `35548010081`, proof commit `e6f038f48b3039df030237424c05be745e33ce24`, artifact `10617142788`, and conclusion `failure`. I recomputed all 12 listed artifact-file hashes without contacting GitHub. The receipt SHA256 is `2d426775791f384f530f4239d1c4fc2e9d05f07658ad8eb6d920021d211d5031`; the project `comparator.log` SHA256 is `f890c287edc9f99a7c7cc777e15b1c92d3c7a1ee51fd56919d90a501ca6918b9`.

The actual log reports the missing `MonicRootSums.olean`, then the earlier Numerics build's interpreter memory exception under `-M4096`, and ends with build failure and `EXIT_STATUS=1`. It establishes neither complete-target Comparator acceptance nor default-kernel acceptance. Successful negative controls are not a success of the target proof. The updated prose correctly says that this log does not isolate the cause of the memory use. The six-root registration repair and local minimal-certificate pass do not retroactively change the failed Linux result, and the local rebuilt package is not described as a successful Linux run.

**Current documentation and referee scopes.** I read the final `VERIFICATION.md` after the coordinator's completed-run update and its last temporal clarification. Its header expressly dates this as the evidence snapshot before the repaired source's Linux run, with later publication evidence linked separately from the canonical problem page. It records the historical pass, isolated numerical pass, complete repaired local pass, and failed first Linux attempt separately, with exact source/run references. That dated-snapshot wording allows the checked project to remain unchanged when later external results are recorded.

`NUMERICAL_TARGETS.md` now describes exactly the implementation previously reviewed at the current Numerics hash: a closed scale-zero rational square-root lower certificate, kernel-mode `leancert_verify_cert`, the proved soundness lemma, the exact sine identity, and a final kernel-trust assertion. It makes no numerical eigenvalue, quadrature, subdivision, native-trust, or parameter-search claim. The new full-run Numerics log contains the expected standard-only axiom report.

`formalization.yaml` accurately names the complete canonical and same-family smooth results, preserves the frozen source identifiers and attribution, and describes local and Linux verification as distinct. Its seven `main_results` names exactly match `comparator.json`; the retained metadata-validation receipt identifies the current YAML and Comparator hashes and a successful seven-declaration schema/coverage check. I inspected that receipt and checked those hashes; I did not rerun its schema validator.

The metadata's two additional final referees are described accurately: nonimplementing statement/premise-discharge and selected proof-assembly/numerical-trust reviews. Neither is relabeled as an independent compiler execution or a fresh proof-line review of all 125 files. I read both reports for scope. Their statements that the repaired full run was still active reflect their earlier review times; this follow-up adds the completed-run evidence, without rewriting their execution claims. All 29 individual input hashes in the final proof referee report match current files, and its clarified string-order aggregate matches the one independently computed here.

Two wording details raised during this audit were resolved before this report was frozen: the Linux memory diagnosis was narrowed to what the log actually proves, and the proof referee's aggregate hash was made explicit in terms of POSIX relative-path-string ordering. Neither required a Lean-source change. No unresolved material evidence or documentation issue remains in this scope.

**Limits.** This report independently checks retained artifacts of a coordinator-run local compiler execution; it is not another compiler run. It does not prove a successful repaired Linux build, Comparator comparison, kernel replay, or sandbox run, and it does not broaden either mathematical referee's source-review scope. It adds no new mathematical resolution or extra distinct-problem verification count.

**Files fixed by this review's hashes.** Relative paths below refer to the authoritative local project. The complete source/log/output maps are in the run record whose hash is listed here.

| File | SHA256 |
| --- | --- |
| `formalization.yaml` | `a34a8d0585de7a572891182a524151c84f090997daac789c4dc943bc6f6d3c98` |
| `NUMERICAL_TARGETS.md` | `aa2e9278007b5f4f9d2e1a6d443d046e8f34d264a4e244eef46648eaf5272d05` |
| `VERIFICATION.md` | `8350b50e8b1e3ba2fb2262f3a4860f530e76b970368f215f8c692ba8e949a40d` |
| `NUMERICS_MINIMAL_CERTIFICATE_STATEMENTS.md` | `ac95aa3b3aee13f8c14ecac1cb15914d98efc0c5c2a91c0babafe2fc7e71b0f9` |
| `MF21Restart/Numerics.lean` | `c4677460fab467e2992c9fd0b1d74abf0d682ba8a7c89857d77e2b481a89e410` |
| `MF21Restart/Definitions.lean` | `35a74047a81a9b7526e9bf039880ca8f07ae33314e2b5b960ab254e02fca4b51` |
| `MF21Restart/TargetProof.lean` | `189eb2e1ed8ad943d78c982e36203cae995e0c6b731293161cb615c9228edf53` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lakefile.toml` | `3237f2e50720c93b153a5179b89ebd9e30f84687193079c9d3628dee99931d31` |
| `lake-manifest.json` | `408ea491dc48a404e8703c56403d3d252fa7bdc4feb393951e34339675a5e2bc` |
| `verify_local.py` | `67b74e0aedc0d6896d1ccaf7e57de3e70b156c56e706e77d6c43703a5ef9a128` |
| `Audit.lean` | `8c3cbee5e8ac2510753fac28633be96c39c24cad70c0f12ebdcdeb89dece35d1` |
| `comparator.json` | `dabddad03ffd9e58d22f1712583ee686d166ede59ebe073798fddd57a928c3ab` |
| `evidence/runs/20260921T005811719722Z/record.json` | `497c98bffe6628a5adef5653adfb73cf25e04fd27f7306176aea9e34260842c5` |
| `evidence/runs/20260921T005811719722Z/Audit.log` | `a1e73e7919dc4a8877bf5e2814c9b225c8781739818459a6170f50d7d646d098` |
| `evidence/logs/numerics-minimal-candidate-02.json` | `80cf97c5c8d989c454d98f2970e0c7a77fa0f2ecccf9e5d7dc58c4d77e38f987` |
| `evidence/logs/numerics-minimal-candidate-02.log` | `cf12e33044415f5b0f465b37eda09124ec5693822d32ad0bb328bce7241777be` |
| `evidence/numerics-minimal-certificate.json` | `cbcf0f850a6080951958e8252d3cf8ec4fa664910094dfb743293483d4a94c85` |
| `evidence/lake-registration-fix.json` | `06f080ec374a8a9eae675ceba9b5b22c639d2e8afe72a7d88c42aa307b0216ba` |
| `evidence/repaired-full-run-integrity.json` | `8d02f3a13278a1acbb21dbd7bf7d29f95a09a9af2a4036debab8b7ce6a153735` |
| `evidence/metadata-validation.json` | `ab68bea67dfdb43241b61f88066f8c051dcbc10b0b52773543248c8ea883a4fb` |
| `reviews/independent-final-statement-review.md` | `6d638666705d5ac5e1baa679e955c8957c97c1d896c7f9466f96f0780c0a1563` |
| `reviews/independent-final-proof-review.md` | `dd3314cd16f23b78a26003d7da0b4d1e849f72137cf8d3d4616d2edf92f4a3db` |

Audit methods: Python `pathlib`, `hashlib`, `json`, `ast`, `re`, and `collections.Counter`; local read-only Git HEAD/cleanliness queries; direct reading of the retained documents and logs. The coordinator integrity receipt was inspected only after my independent comparisons. No audit script was imported or executed as a compiler runner.

Report frozen UTC: 2026-09-21T01:21:20.181064+00:00
