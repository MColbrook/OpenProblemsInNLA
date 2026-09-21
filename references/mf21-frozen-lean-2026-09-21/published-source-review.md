# Published MF-21 source and packaging review

Reviewer: `mf21_restart_lean_audit`. No Lean compiler, Lake build, or Comparator was run by this reviewer. This audit is outside the proof project so that historical published proof inputs remain identifiable.

**Verdict for commit `e6f038f48b3039df030237424c05be745e33ce24`: source correspondence PASS; CHANGES_REQUESTED for fresh-build readiness.** The exact proof bodies, pins, contracts, and retained local evidence match their recorded versions, but the first actual Linux run failed during the Solution build: a vendored module was not registered with Lake, and the Numerics interpreter exceeded its configured memory limit. Both failures and the separate six-root configuration repair are recorded below. This report must not be used as a readiness or Comparator-success certificate for this original candidate.

## Exact publication and local-record correspondence

The inspected Git commit is `e6f038f48b3039df030237424c05be745e33ce24`, parent `5089cc23ab223234b9d7a73a9501123d1180de5d`. The exact project is:

    matrix-functions-and-stability/MF-21/lean-frozen-2026-09-12

Files were read from committed blobs with `git show <commit>:<project>/<path>`, not inferred from the changing worktree. The retained local record is `evidence/runs/20260921T000301098707Z/record.json`, SHA256 `abdf520ffbcfc2fe80236e0c303795d97a50e8c11f46a5edbac8a29dba5d7856`. Its committed bytes equal the original development record and the committed `evidence/latest-local.json`.

The reviewer independently compared:

- all **125** committed Lean source blobs with every entry of that record's `source_hashes`;
- all **three** pinned configuration blobs with `pin_hashes`;
- all **125** committed local compiler logs with their recorded hashes and zero exit statuses;
- the archived exact runner and the frozen manuscript with their recorded hashes;
- all **386** actual axiom reports with Audit's complete distinct declaration list and the permitted standard-axiom set.

Every comparison matched. The committed project's `.lean` file inventory is exactly those 125 recorded sources: no recorded Lean file is missing, and no extra Lean file is outside that source list. No `.lake` content or compiled `.olean`, `.ilean`, `.o`, `.so`, or `.a` artifact is committed in the project.

The local run itself is historical execution evidence from the coordinator. The current local `.lake/build` outputs were removed **after** the earlier complete source/log/output hash check. This publication review does not claim those binaries remain present and does not recompute their hashes now. Their hashes remain in the immutable run record; the earlier independent comparisons are documented in the published Target and metadata reviews. The publication check above compares retained source and log blobs, not absent compiled outputs.

## Reviewed target and contract identities

| Committed item | SHA256 |
|---|---|
| `MF21Restart/Definitions.lean` | `35a74047a81a9b7526e9bf039880ca8f07ae33314e2b5b960ab254e02fca4b51` |
| `MF21Restart/TargetProof.lean` | `189eb2e1ed8ad943d78c982e36203cae995e0c6b731293161cb615c9228edf53` |
| `Challenge.lean` | `9bb51fae68bab7a4ba5ff8fe7c3b815e361f31c041897ee04596dfd0215989b2` |
| `Solution.lean` | `97dffa0a35b7067b784763adcdf01c21f8da7d005a69c32662dbe9c84e080659` |
| `comparator.json` | `dabddad03ffd9e58d22f1712583ee686d166ede59ebe073798fddd57a928c3ab` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lakefile.toml` in this original candidate | `72d7312e69cec52c85a3ad536f18d71d6e41603040a5717b298018374b8343f3` |
| `lake-manifest.json` | `408ea491dc48a404e8703c56403d3d252fa7bdc4feb393951e34339675a5e2bc` |
| `original-proof/solution.md` | `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa` |
| `original-proof/problem.md` | `1aac38ed3c7a83dfc3dddb4beeec26fcf117f23f5789b2a374c1332ba4cf359f` |

These are the exact target/statement/proof versions already reviewed, not replacement theorems. The seven committed Challenge and Solution signatures again match textually after whitespace normalization, and their fully qualified names match `comparator.json` exactly:

1. `MF21Restart.Contracts.complex_fourier_eq_cosine`
2. `MF21Restart.Contracts.bulk_cutoff_pos`
3. `MF21Restart.Contracts.critical_bound_implies_fixed_index_limit`
4. `MF21Restart.Contracts.exists_log_sq_bulk_scale_gain`
5. `MF21Restart.Contracts.phase_window_margin`
6. `MF21Restart.Contracts.manuscript_smooth_target`
7. `MF21Restart.Contracts.target_proved`

Only `propext`, `Quot.sound`, and `Classical.choice` are permitted. The complete Target is unconditional and uses one coefficient family; the stronger theorem gives that same family smooth regularity. The seven intentional Challenge placeholders remain outside the proof import closure. This is a source-identity/contract check, not a new independent proof review of components authored by this reviewer. All author exclusions in the earlier reviews remain in force.

The committed Target review has SHA256 `c6ca04dedf05858b286cc4b6cab2407848231818d8eb2e273ce4d58e2734ae1e`; the metadata review has SHA256 `6a4f271a5461fe9ebc7308eadd77c279f3e6c33c02c6533b79ab04c1ae3e5330`. The committed metadata, SHA256 `3448a61dc1a77ea9e13dd672ad4be93544f0aabf5f4123850b7896ec1368e3a3`, and validation record, SHA256 `24ed9b128b26e4805f5630c22f3ac1fa4af82128b8724ea8550e1452adb64910`, match the final locally reviewed versions. Their schema/coverage result is not a fresh-build or Comparator result.

## Archived and portable runner distinction

The full local proof run used the archived runner SHA256 `fddada659794fdf62748ffc0790368c30b1bf66ff0acc939161edbd1fd4b8d85`. The archive is committed beside the immutable run record. The distributed portability-only revision is SHA256 `67b74e0aedc0d6896d1ccaf7e57de3e70b156c56e706e77d6c43703a5ef9a128`, with its separate Python smoke record SHA256 `b9d7f269d82018fcd0567ed760c4561d861464c296129800af72fb96b723cabe`.

The committed `VERIFICATION.md`, SHA256 `3695d1339977f1c417f27e0b67cdfce4c7c90f9abbf5ab01bca4e91a0c68bafc`, adds the accurate note that the later portability test is neither another Lean compilation nor a Comparator run. That note matches the retained evidence. The reporter authored the small portability change and does not claim independent review of that contribution here.

## Material packaging finding after publication

The original candidate's `lakefile.toml` registers the `LeanFormalizations` library with only this root:

    LeanFormalizations.NumberTheory.Transcendence.PiTranscendental

The other five vendored transcendence files are siblings of that module, not submodules of it. The pinned Lake source at `Lake/Config/LeanLibConfig.lean:31–46` states that roots include their submodules and that default globs are the exact roots. Its `isLocalModule` implementation at lines 123–125 uses root-prefix membership or a matching glob. Therefore the sibling modules are not registered by that original declaration.

The coordinator reported an actual local no-build/no-cache resolution check of

    lake --no-build --no-cache build +LeanFormalizations.NumberTheory.Transcendence.ETranscendental

returning exit 1 with an unknown-module diagnostic. This reviewer did not execute that command. The source-level registration defect was independently checked against the pinned Lake definitions. Direct serial `lake env lean` compilation of all six files had produced the needed local outputs, which explains why the earlier local proof run could pass without exercising this fresh Lake module-discovery path.

The required repair is to register all six exact vendored modules, then retain the actual resolution checks and a new source-matched serial run binding the changed Lakefile hash. No mathematical proof-body change is implied by that registration repair. The original local proof evidence remains genuine for its recorded direct-compilation commands, but it does not establish that this original candidate can build freshly through the Comparator harness. **The original GitHub run failed; it was not cancelled. No Comparator PASS at commit `e6f038f...` is claimed.** A later corrected commit and its evidence require a distinct review entry; the old pin hash must not be silently relabelled as the repaired one.

## Separate static review of the six-root repair

**APPROVE for the registration repair's source scope only.** The repaired development `lakefile.toml` has SHA256 `3237f2e50720c93b153a5179b89ebd9e30f84687193079c9d3628dee99931d31`. A byte comparison with the published original confirms that the only change is the `LeanFormalizations` roots array. It now lists exactly the six existing source modules:

    LeanFormalizations.NumberTheory.Transcendence.ETranscendental
    LeanFormalizations.NumberTheory.Transcendence.PiLindemann
    LeanFormalizations.NumberTheory.Transcendence.HermiteLindemann
    LeanFormalizations.NumberTheory.Transcendence.MonicRootSums
    LeanFormalizations.NumberTheory.Transcendence.SubsetSumEsymm
    LeanFormalizations.NumberTheory.Transcendence.PiTranscendental

The reviewer compared that set with the entire vendored `.lean` inventory: no source is missing or newly introduced. Pinned Lake's root-prefix/glob membership rules now include all six modules. All library arguments remain `-j1 -M4096`; the toolchain, dependency manifest, and comparator configuration are byte-for-byte unchanged. The archived old Lakefile at `evidence/runs/20260921T000301098707Z/lakefile.toml` is exactly the old published file, SHA256 `72d7312e69cec52c85a3ad536f18d71d6e41603040a5717b298018374b8343f3`.

The retained coordinator record `evidence/lake-registration-fix.json`, SHA256 `06f080ec374a8a9eae675ceba9b5b22c639d2e8afe72a7d88c42aa307b0216ba`, records an actual no-build/no-cache check for each of the six roots. All six are recognized and return exit 3 because their outputs need rebuilding; none returns the original unknown-module error. These are successful **resolution checks**, not successful Lean builds. The reviewer read and hashed the record but did not run Lake.

At this inspection, every one of the 125 development Lean sources still matched the original immutable run's source hashes, including Numerics SHA256 `9d8eb86229773759393cecd14b2651dfc6a994c270dc1ee82d3131c1af60bc42`. A planned certificate-cost change is a separate proof revision and is not covered by this configuration approval. The repaired pin and any such revision require their own local execution and publication evidence.

## Additive canonical-page diff

The committed diff from publication base `aa8d010bdd5a3ef1750c9fa013b67b6d90786d96` to `e6f038f...` changes neither the canonical MF-21 README, `RESOLVED.md`, `problem_ids.json`, the root catalog README, nor the existing `MF-21/lean` project. The only infrastructure addition is the separate dedicated workflow; shared tools and the generic workflow are unchanged.

At inspection, the proposed canonical README and RESOLVED additions were **uncommitted worktree drafts**, not part of `e6f038f...`. The diff adds six lines to `matrix-functions-and-stability/MF-21/README.md` and one line to `RESOLVED.md`, with zero deleted lines. An independent line-subsequence check confirms that every original line is retained in order. The additions link the separate frozen-manuscript project, describe the same-family theorem and local run, retain George Stepaniants's affiliation and AI-assistance disclosure, and expressly deny any extra distinct-target count. The original target, status, previous proof attribution, and counts are unchanged.

The exact draft hashes at this inspection were `c9e073b7d221011db53dc2e20c8c706887e3c45140db0d8602167b3cc25f1ba1` for the canonical README and `2219ebe206dab0ee9419658e2b7c226430519223fa28e870685d8360038c0548` for RESOLVED. The corresponding committed hashes at `e6f038f...` are `e76acaba997afe67a0df0c5d3aff23e55aaf700e577e8458cd2709e874c0370c` and `9354395c6650b23aa374f07fcff94973817cf07d79a782ee8bbca335ae537788`.

Those drafts must point to the eventual actually checked repaired commit and run, and the referenced publication-evidence README must exist before they are presented as completed runtime evidence. Their additive target/status/count behavior is approved; this report does not approve a pending run as successful or obsolete links as final.

## Dedicated workflow and actual first Linux attempt

The committed dedicated workflow SHA256 is `eb8a5aecaefab354c61825e5bd3ad1d31b53a7ca880192756581529e8b299012`. It has one job with the literal `LEAN_PROJECT` path above, passes that same value to metadata validation and `tools/lean/verify.sh`, and preserves the previously reviewed no-prebuild fresh-check design. Shared harness and source-lock hashes are respectively `f81767a17973956fbe9e5765c664d4639cce15ddf8c106f70cdcb32151808c2f` and `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`.

The complete earlier static workflow review is committed in the proof project's `reviews/publication-workflow-review.md`. The first actual attempt is [GitHub run 35548010081](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35548010081), at the original `e6f038f...` commit, with conclusion **failure**. The cancellation request was too late and did not cancel the run. The receipt [linux-attempt-01.json](linux-attempt-01.json), SHA256 `2d426775791f384f530f4239d1c4fc2e9d05f07658ad8eb6d920021d211d5031`, identifies artifact `10617142788`. The reviewer recomputed all 12 downloaded file hashes: every hash matched, with no missing or extra artifact file.

The downloaded logs distinguish successful verifier controls from the failed MF-21 Solution build:

- [kernel-controls.log](linux-attempt-01/verify-20260921T003354Z-4172/kernel-controls.log), lines 8–25, records acceptance of the honest fixture, rejection of an invalid raw proof, and rejection of a quotient post-check mismatch; the script exits 0. These are the three actual kernel-control cases, not MF-21's target replay.
- [comparator-controls.log](linux-attempt-01/verify-20260921T003354Z-4172/comparator-controls.log), lines 4–79, records the five expected regression outcomes and exits 0. Its `Your solution is okay!` marker belongs to the small `simple_match` fixture.
- [negative-sorry.log](linux-attempt-01/verify-20260921T003354Z-4172/negative-sorry.log), line 13, rejects `sorryAx`; [negative-native.log](linux-attempt-01/verify-20260921T003354Z-4172/negative-native.log), line 12, rejects the native-decision axiom. Both fixtures exit 1 as required. These diagnostics are expected controls, not the project failure.
- [sandbox.log](linux-attempt-01/verify-20260921T003354Z-4172/sandbox.log) records successful build/export isolation probes and expected option-policy rejections. This is evidence for those probes, not an unrestricted security guarantee.
- The actual project [comparator.log](linux-attempt-01/verify-20260921T003354Z-4172/comparator.log), SHA256 `f890c287edc9f99a7c7cc777e15b1c92d3c7a1ee51fd56919d90a501ca6918b9`, fails first at line 172 because `PiTranscendental` cannot find `MonicRootSums.olean`. At lines 1007–1011, Numerics is invoked with `-j1 -M4096` and its interpreter throws `lean::memory_exception`, followed by Lean exit 134. Lines 1012–1016 list both failed required targets and the unsuccessful build. Neither final acceptance marker occurs anywhere in this project log.

The separately retained GitHub job log `/private/tmp/mf21-verifier-tools/linux-first-failed.log`, SHA256 `03dd218902f6918f3abe61bdba275ba4de9d39fa59e6dda394449899c4c0ff94`, timestamps the missing module at `2026-09-21T00:38:36.7410868Z`, the memory exception at `00:43:17.3662628Z`, and final process exit 2 at `00:43:22.5178222Z`. The GitHub completion time reported by the coordinator is `00:43:26Z`.

A later local diagnostic record, `evidence/logs/numerics-lake-shape-01.json`, SHA256 `fefcb8f9b0224874f081cd59f5af55442247fa0d6ee01adfdd69fff5cb78fff2`, reports exit 0 for the unchanged Numerics with direct Lean `-o`, `-i`, `-c`, and `--json` output options. Its log hash matches `0e95fe77aec27fcc889d8daeeb0108768939339ecda8ce613cd020e0899c2755`. As that record explicitly says, it does not replay Lake's actual `--setup` invocation and does not cure or supersede the observed Linux failure.

There is **no final MF-21 Comparator acceptance or kernel replay acceptance** from this first attempt. Source correspondence, successful controls, metadata validation, and the genuine local Lean run do not substitute for that result. No completed-verification count is added by this report.
