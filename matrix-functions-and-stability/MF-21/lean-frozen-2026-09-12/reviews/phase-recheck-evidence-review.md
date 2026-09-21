**MF-21 phase repair: independent local evidence audit**

**Verdict: APPROVE for the current local evidence and validated reuse scope.** The complete current-source evidence consists of ten successful new compilations and 115 verified reused outputs. No source, configuration, dependency, import-closure, log, output, or axiom mismatch was found. This is not a Linux Comparator, kernel-replay, or sandbox acceptance.

Reviewer: Codex agent `mf21_final_proof_referee`, 21 September 2026 UTC. I did not implement the repair or either compiler runner. I read `evidence/recheck_phase_dependents.py` without executing it, independently reconstructed the local import graph, and inspected actual retained records, logs, sources, outputs, and dependency checkouts. My tools were read-only Python/Git inspections; I ran no Lean compiler, Lake build, push, or workflow. I wrote only this external report. This is an execution-evidence audit under the project's pinned referee standards, not a broader mathematical proof review.

The inspected staging project is `/Users/georgestepaniants/Research/OpenProblemsInNLA/lean-verification/MF21-restart`. The completed recheck record is `evidence/runs/20260921T014829335357Z-phase-recheck/record.json`, SHA256 **`bcb21102dcd847a244595c04f6cd759b7221b4bd0c0e674beef969ed6eea9c3a`**. It records coordinator execution from `2026-09-21T01:48:29.335357+00:00` through `2026-09-21T01:50:06.082402+00:00`. `evidence/latest-phase-recheck.json` is byte-identical. The independent comparisons below completed at `2026-09-21T01:54:01Z`.

I independently found exactly **125 current Lean sources**, matching the record's complete source-hash map. Only `MF21Restart/PhaseWindowRoots.lean` differs from the successful baseline record `evidence/runs/20260921T005811719722Z/record.json`, whose SHA256 remains `497c98bffe6628a5adef5653adfb73cf25e04fd27f7306176aea9e34260842c5`. The current source aggregate is `caeeae26898daf43b5d52d11042e8c033dbb9ef8aafe21784c34313d087e4e4f`: sort POSIX relative-path strings, concatenate UTF-8 `<SHA256><two spaces><relative path><LF>` lines, then hash.

After stripping nested comments and strings, I parsed current import declarations independently of the one-off runner. The resulting local graph equals the recorded graph. Reverse transitive closure from the sole changed source yields exactly these ten files, in the actual recompilation order:

1. `MF21Restart/PhaseWindowRoots.lean`
2. `MF21Restart/PhaseWindowIndexing.lean`
3. `MF21Restart/PhaseQuantitative.lean`
4. `MF21Restart/ImplicitSpectralError.lean`
5. `MF21Restart/ImplicitSpectralData.lean`
6. `MF21Restart/ImplicitExpansionBounds.lean`
7. `MF21Restart/TargetProof.lean`
8. `MF21Restart.lean`
9. `Solution.lean`
10. `Audit.lean`

Every local dependency precedes its user in the source order. The recorded reused set is exactly the other **115 sources**, with no duplicate or omission; none has a transitive local dependency on the changed phase module. The unchanged Challenge correctly belongs to the reused set.

All ten recorded commands are exactly `lake env lean -j1 -M4096 -o .lake/build/lib/lean/<source without .lean>.olean <source>`, each with `LEAN_NUM_THREADS=1` and exit zero. I recomputed all ten actual log hashes, their output hashes, and the record's complete 125-output map. Every current `.olean` matches. For each reused source I separately matched its current source hash, current output hash, baseline source/output hashes, successful baseline log identity and hash, and baseline exit zero. All 125 baseline log hashes still match the baseline record. This audit does not claim to rehash the ten historical affected outputs after they were replaced; the inspected one-off runner explicitly checked all baseline output hashes before recompilation, and I independently checked the 115 outputs actually reused plus the ten newly produced outputs.

I read the one-off runner's whole implementation. It binds the exact baseline record and changed phase-source hash, validates the source inventory and dependency order, checks source/pin/runner/manuscript compatibility and baseline logs/outputs, checks external package HEADs and tracked cleanliness, and runs affected sources serially under the shared compiler lock. Its success path rechecks source and pin hashes and requires all 386 Audit reports. I did not execute or import this runner as code; parsing its companion full-runner source list used `ast.literal_eval` only.

I also independently queried all **ten external package checkouts** using read-only Git commands with optional locks disabled. Every HEAD equals its manifest revision and both records' package HEAD entries, and every tracked tree is clean. The Mathlib and LeanCert revisions remain `0df444a360eaa60ab8c11dca51a86af692955474` and `621a43d7cf21f87872392a01e874f2f1dbddc926` respectively. All three current configuration hashes match the recheck record; the toolchain, dependency manifest, full local runner, and frozen manuscript retain their baseline hashes.

The archived baseline Lakefile matches its original recorded hash. Comparing it byte-for-byte with the current Lakefile confirms **exactly four** substitutions of `"-M4096"` by `"-M6144"`, all in library `moreLeanArgs`; reversing those substitutions reproduces the archived file exactly. No dependency or other Lake setting changed. The 6144 MiB library ceiling is not intrinsically Linux-only: ordinary local `lake build` would also receive it. The actual local recheck and unchanged full runner explicitly use **4096 MiB and one thread**, as required. This report does not claim that the higher Lake ceiling or proof optimization resolves the Linux failure.

I parsed the actual new `Audit.log` independently, including multiline lists. Its **386 unique reports** exactly match the 386 `#print axioms` declarations in the current `Audit.lean`, with no omitted or duplicate name. Every parsed set equals the record and is a subset of `{propext, Classical.choice, Quot.sound}`. Complete-target and contract reports are present. The Audit log SHA256 is `a1e73e7919dc4a8877bf5e2814c9b225c8781739818459a6170f50d7d646d098`.

| Reviewed input | SHA256 |
|---|---|
| Current `MF21Restart/PhaseWindowRoots.lean` | `7992ba76a6919b9e38aa3758ff74205befe02238e515b66b96584c1848a8d5c8` |
| Current `lakefile.toml` | `a44cbbbcb0c57a23ac33ba4503d21e59a3205df717a93a547b1ad897b92da9f4` |
| Archived baseline `lakefile.toml` | `3237f2e50720c93b153a5179b89ebd9e30f84687193079c9d3628dee99931d31` |
| `evidence/recheck_phase_dependents.py` | `7c5686615e8f66e780635b5b1f948299954d88833132cb423acc2cf177e6ad9c` |
| Unchanged `verify_local.py` | `67b74e0aedc0d6896d1ccaf7e57de3e70b156c56e706e77d6c43703a5ef9a128` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lake-manifest.json` | `408ea491dc48a404e8703c56403d3d252fa7bdc4feb393951e34339675a5e2bc` |
| Frozen `original-proof/solution.md` | `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa` |
| New `PhaseWindowRoots.log` | `9e4625708663d3fbe14d1eb67bbf5a59401b8674e06985c006d9bd34189dd1c4` |
| New `PhaseWindowRoots.olean` | `ee0bab084a9e78345eaef1aaabb1bda22be6d6de122a2964909a09d43262aafb` |

The separate statement referee's `phase-memory-repair-review.md`, SHA256 `6c70b00ee5a9c98ca547d248913551ff1a41de98a0f62f42e974d5f25c87cfdd`, covers the unchanged theorem statements and twelve restricted arithmetic tactic calls at the current phase-source hash. I read that report to preserve its scope; this evidence audit does not reissue its mathematical conclusions. The previously failed Linux runs remain failed, and this recheck explicitly records `comparator: not_run`. A later published-source binding and actual Linux acceptance need separate evidence. No new resolution or completed-verification count is added here.
