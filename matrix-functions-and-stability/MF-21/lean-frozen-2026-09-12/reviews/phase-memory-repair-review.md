# MF-21 phase-window memory repair review

**Verdict: APPROVE the identified source and resource-only configuration changes, within the scope below.** This is not a whole-target re-review or a successful Linux acceptance.

Reviewer: independent Codex agent `/root/mf21_final_statement_referee`, 21 September 2026 UTC. I did not implement the changes, run Lean/Lake, invoke GitHub, or edit proof/configuration files. I read the complete original PhaseWindowRoots source and candidate diff, candidate record/log, Lakefile, local runner, and retained second Linux failure. The project's `REFEREE_STANDARDS.md` applies. After review I checked that the candidate and the exact four-flag configuration change had been installed canonically.

The source changes exactly twelve calls to explicit `linarith only` inputs already present in context. All seven theorem/definition headers are identical by independent text comparison. Imports, definitions, hypotheses, conclusions, quantifiers, ranges, and the public theorem are unchanged. I checked that the selected facts suffice: the derivative step combines the established main-term and error lower bounds; window membership uses the corresponding monotonicity or absolute-value inequality; endpoint signs use the existing sine margin and error bound; the remaining bounds use the same pi positivity and index/phase order. The increasing-phase, intermediate-value, monotone-residual, uniqueness, and nonzero-derivative argument is unchanged. No assumption, approximation, axiom, or trust shortcut is introduced.

The actual candidate record `/private/tmp/mf21-phase-memory-tests/candidate-01/record.json` records local execution from `2026-09-21T01:37:31.726573+00:00` to `01:37:47.043446+00:00`, exit zero, `LEAN_NUM_THREADS=1`, and `lake env lean -j1 -M4096 -R /private/tmp /private/tmp/MF21PhaseWindowRootsCandidate.lean`, with `.olean`/`.ilean`/C emission, `--profile`, and `--json`. I matched the source, actual log, and all three output hashes. Its actual public-theorem axiom report contains only `propext`, `Classical.choice`, and `Quot.sound`. The record reports maximum child RSS of 3,649,159,168 bytes on macOS. I did not independently measure it, infer a Linux peak, or claim a material memory reduction. This is an isolated local pass; affected-package integration and Linux execution need separate evidence.

The installed configuration changes only four library `moreLeanArgs` flags from `-M4096` to `-M6144`, retaining `-j1`. No dependency/toolchain pin, contract, permitted axiom, kernel setting, Comparator harness, sandbox policy, or manuscript change belongs to this repair. Increasing a compiler resource ceiling does not weaken proof checking. The unchanged local runner still explicitly invokes `lean -j1 -M4096` with `LEAN_NUM_THREADS=1` under a serial compiler lock.

**Constraint communicated before installation:** TOML `moreLeanArgs` is not operating-system conditional; an ordinary local `lake build` would also receive 6144 MiB. Local development must therefore continue through the unchanged explicit-4096 runner or an equivalently explicit permitted command. The package default should not be described as intrinsically Linux-only. With that stated workflow preserved, I find no objection to the 6144 MiB ceiling for Linux Lake/Comparator. Neither this ceiling nor the arithmetic restriction is asserted to have resolved the Linux failure.

The retained receipt identifies Linux run `35550709155`, commit `bd3014e699f277500beabda57cfeb1f57925ab78`, artifact `10617913898`, and **failure**. I checked all twelve artifact hashes and the decisive project log: PhaseWindowRoots ran with `-j1 -M4096`, terminated with an interpreter memory exception and exit 134, and the build ended with `EXIT_STATUS=1`. The cause of the memory pressure is not isolated. There was no complete-target Comparator/default-kernel acceptance. Earlier complete-package records remain historical after this source/configuration change.

| Input | SHA256 |
| --- | --- |
| Original PhaseWindowRoots source reviewed before installation | `7ababccde85698a360037679ab6d314ca6582f97a0cc09a3a320a38deb7a4590` |
| Candidate and now canonical `MF21Restart/PhaseWindowRoots.lean` | `7992ba76a6919b9e38aa3758ff74205befe02238e515b66b96584c1848a8d5c8` |
| Candidate `record.json` | `237d3985c34879f98722675aa826d1514b994aa120c317808b7aea1c8e5f5519` |
| Candidate `compile.log` | `1170ac43a02555af0a09328376f8086b9dfe0c116bc803c3f853baea9be68284` |
| Lakefile before resource change | `3237f2e50720c93b153a5179b89ebd9e30f84687193079c9d3628dee99931d31` |
| Installed Lakefile: exactly four flag substitutions | `a44cbbbcb0c57a23ac33ba4503d21e59a3205df717a93a547b1ad897b92da9f4` |
| Unchanged `verify_local.py` | `67b74e0aedc0d6896d1ccaf7e57de3e70b156c56e706e77d6c43703a5ef9a128` |
| `linux-attempt-02.json` | `a23b152ce72d78acdb24a34ef82710160a7d7e9198325bf426983a396b004967` |
| Second Linux project `comparator.log` | `32f18010bb8babfe443d39c0f9d841ea8098090a24139cdbe553aa8fd9c952d7` |

This scoped review adds no new resolution or completed-verification count.

Report UTC: 2026-09-21T01:48:29.447847+00:00
