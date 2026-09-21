# MF-21 repaired-package evidence review

**Verdict: APPROVE for the local evidence and its documented scope.** The repaired package matches a completed successful local Lean run and its 386 actual axiom reports. No successful repaired-source Linux Comparator, kernel replay, or sandbox execution is claimed.

Reviewer: Codex agent `/root/mf21_final_statement_referee`, 21 September 2026 UTC. I did not author the proof, repair, runner, or compiler records. This follow-up checks retained evidence and the final documentation under `reviews/REFEREE_STANDARDS.md`; it is not another compiler run or a broader mathematical review. I edited only this new report, invoked no Lean/Lake build or GitHub command, and made no network query. The reviewed project is `lean-verification/MF21-restart`.

**Independent completed-run audit.** The repaired record `evidence/runs/20260921T005811719722Z/record.json`, SHA256 `497c98bffe6628a5adef5653adfb73cf25e04fd27f7306176aea9e34260842c5`, records execution from `2026-09-21T00:58:11.719722+00:00` through `2026-09-21T01:13:32.503384+00:00`. I checked the underlying files and logs, independently of its `passed` flag and the coordinator integrity receipt:

- All **125 current source hashes** match. The source set equals every root `.lean` file and every `.lean` file under `MF21Restart/` and `LeanFormalizations/`. Parsing the runner's `MODULES` assignment with `ast.literal_eval`, without executing the runner, confirms the same 125 unique sources and recorded order. This includes all six vendored modules, the full assembly, wrappers, and Audit.
- All **three pin-file hashes**, the runner hash, and the frozen manuscript hash match. Archived copies of the runner and Lakefile beside the new record also match current bytes. The manuscript remains `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`.
- All **125 commands, environments, and exit codes** match: `lake env lean -j1 -M4096 -o .lake/build/lib/lean/<module>.olean <source>.lean`, `LEAN_NUM_THREADS=1`, and exit zero. The inspected runner serializes blocking invocations under its shared compiler lock.
- All **125 retained log hashes** and **125 current compiled-output hashes** match. Output paths were independently reconstructed from source names and checked against command arguments.
- All **ten dependency checkout HEADs** equal both the manifest and recorded revisions, with no tracked edits. I used read-only Git HEAD/status queries with optional locks disabled. Mathlib is pinned at `0df444a360eaa60ab8c11dca51a86af692955474`; LeanCert at `621a43d7cf21f87872392a01e874f2f1dbddc926`.
- All **386 actual axiom reports** parsed directly from `Audit.log` exactly match the 386 unique `#print axioms` names independently extracted from `Audit.lean`, with no duplicate or omission. Parsed axiom sets match the record and contain only `propext`, `Classical.choice`, and `Quot.sound`. The actual log contains no `sorryAx`; complete-target reports are present.

No mismatch was found. `evidence/latest-local.json` is byte-identical to the completed record. The 125-source aggregate is `0dc27e2cca2a98b89580bddfc6f6ad8e3a06e0524c690a4886e9c89030bdc023`: sort POSIX relative-path strings, concatenate UTF-8 `<SHA256><two spaces><relative path><LF>` lines, then hash. Per-source, per-command, per-log and per-output details remain in the identified record.

**Execution distinctions.** The historical `20260921T000301098707Z` record has SHA256 `abdf520ffbcfc2fe80236e0c303795d97a50e8c11f46a5edbac8a29dba5d7856`. Its 125 exit codes are zero and all 125 retained log hashes match. Only Numerics differs from its source map, and only Lakefile differs from its pin map; archived old copies match the old hashes. That earlier pass is correctly described as historical. Current compiled outputs were not treated as archived historical outputs.

The isolated candidate record `evidence/logs/numerics-minimal-candidate-02.json` identifies the current Numerics hash `c4677460fab467e2992c9fd0b1d74abf0d682ba8a7c89857d77e2b481a89e410`, a zero exit, one thread and 4096 MiB, with `.olean`/`.ilean`/C emission and JSON diagnostics. I verified its source, temporary-candidate byte equality, and actual log hash, and parsed its standard-only margin-theorem axiom report. The candidate result and later complete repaired run remain separate local checks.

The retained first Linux receipt identifies run `35548010081`, commit `e6f038f48b3039df030237424c05be745e33ce24`, artifact `10617142788`, and **failure**. I rehashed all 12 listed retained artifact files without contacting GitHub and read the decisive project build log. It reports missing `MonicRootSums.olean`, Numerics' interpreter memory exception under `-M4096`, and `EXIT_STATUS=1`. It provides no complete-target Comparator or default-kernel acceptance; negative-control successes do not change that outcome. Receipt SHA256: `2d426775791f384f530f4239d1c4fc2e9d05f07658ad8eb6d920021d211d5031`. Project log SHA256: `f890c287edc9f99a7c7cc777e15b1c92d3c7a1ee51fd56919d90a501ca6918b9`. These files were inspected under publication `references/mf21-frozen-lean-2026-09-21/`.

**Documentation and review scope.** I read the final `VERIFICATION.md`, including its last header update: this is a dated evidence snapshot before the repaired source's Linux run; later publication evidence is linked separately from the canonical page. It accurately separates the historical pass, isolated repair pass, completed repaired local pass, and failed Linux attempt.

`NUMERICAL_TARGETS.md` accurately describes the reviewed scale-zero rational square-root certificate, kernel-mode `leancert_verify_cert`, proved soundness lemma, exact sine identity, and kernel-trust assertion. `formalization.yaml` retains frozen-source attribution and separates local results from Linux evidence. Its seven main-result names exactly match `comparator.json`. The retained schema/coverage receipt matches the current YAML and Comparator hashes; I inspected that receipt without rerunning its validator.

The metadata correctly describes both final referees as nonimplementing reviewers of statement/premise discharge and selected proof-assembly/numerical-trust scopes. Neither is credited with a fresh review of all proof lines or an independent compiler execution. Their earlier “run active” observations remain accurate historical snapshots; this report supplies the later completed-run audit. All 29 individual hashes in the final proof referee report match, as does its clarified aggregate.

Two precision issues raised during this audit were resolved before freezing: the Linux memory wording now reports the observed interpreter exception without claiming its cause was isolated, and the proof referee's aggregate now explicitly uses relative-path-string ordering. Neither required changing a Lean source. No unresolved material documentation or evidence issue remains in this scope.

**Limits.** This is independent artifact verification of a coordinator-run local compilation, not another compilation, Linux acceptance, or extension of the mathematical reviews. It adds no new resolution or distinct-problem count. Audit methods were Python `pathlib`, `hashlib`, `json`, `ast`, `re`, and `collections.Counter`, read-only Git queries, and direct document/log reading.

**Reviewed file hashes.** Complete source/log/output maps are retained in the identified run record.

| File | SHA256 |
| --- | --- |
| `formalization.yaml` | `a34a8d0585de7a572891182a524151c84f090997daac789c4dc943bc6f6d3c98` |
| `NUMERICAL_TARGETS.md` | `aa2e9278007b5f4f9d2e1a6d443d046e8f34d264a4e244eef46648eaf5272d05` |
| `VERIFICATION.md` | `8350b50e8b1e3ba2fb2262f3a4860f530e76b970368f215f8c692ba8e949a40d` |
| `MF21Restart/Numerics.lean` | `c4677460fab467e2992c9fd0b1d74abf0d682ba8a7c89857d77e2b481a89e410` |
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
| `evidence/repaired-full-run-integrity.json` | `8d02f3a13278a1acbb21dbd7bf7d29f95a09a9af2a4036debab8b7ce6a153735` |
| `evidence/metadata-validation.json` | `ab68bea67dfdb43241b61f88066f8c051dcbc10b0b52773543248c8ea883a4fb` |
| `reviews/independent-final-statement-review.md` | `6d638666705d5ac5e1baa679e955c8957c97c1d896c7f9466f96f0780c0a1563` |
| `reviews/independent-final-proof-review.md` | `dd3314cd16f23b78a26003d7da0b4d1e849f72137cf8d3d4616d2edf92f4a3db` |

Report frozen UTC: 2026-09-21T01:22:49.911395+00:00
