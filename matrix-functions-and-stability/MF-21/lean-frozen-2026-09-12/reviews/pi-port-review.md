# Independent π dependency port and bridge review

Verdict: **APPROVE** the reviewed port deltas and exact unconditional bridge. The coordinator has now completed actual local compilation of the six-file closure and bridge on the pinned Lean/Mathlib 4.33.1 environment, with one thread and a 4096 MiB limit. The final bridge's observed axiom output is exactly `[propext, Classical.choice, Quot.sound]`. I ran no compiler, kernel/Comparator executable, Lake build, or GitHub workflow. This is independent source/statement review informed by the coordinator's actual local results, not a claimed independent rerun. No Comparator run or complete MF-21 target result is recorded.

## Upstream comparison

I compared each local file byte-for-byte and by full unified diff with the small sources downloaded from immutable gotrevor commit `3a24a73416f83c32b4d4a2ac09588524c6291650`. The exact diffs and hashes are retained in `pi-port-source-comparison.json` beside this report. Four files are byte-identical: ETranscendental, PiLindemann, HermiteLindemann, and PiTranscendental.

In `MonicRootSums.lean:23–29`, only the explanatory comment and imports changed. Umbrella `import Mathlib` was replaced by `Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities` plus `Mathlib.Tactic`; both original local imports remain. Every declaration and proof body is unchanged. The first broad-import attempt reached the imposed memory limit; narrowing imports is a resource accommodation, with no mathematical premise added.

In `SubsetSumEsymm.lean:18–23`, umbrella Mathlib became targeted imports for symmetric-polynomial fundamental theorem, complex polynomial basics, algebraic closure, Vieta, and Mathlib tactics. At line 38, one proof step also changed: the empty-multiset branch now supplies `Multiset.powersetCard_zero_right` explicitly to `simp +decide`. This is **not** an import-only port. The exact pinned Mathlib theorem, `Data/Multiset/Powerset.lean:256`, proves that a positive-cardinality powerset of the empty multiset is empty, with proof `rfl`; it has no hypothesis or external assumption. This resolves the actual prior empty/successor goal. Every declaration statement and all remaining proof text are unchanged. It introduces neither a weaker theorem nor a trust extension.

Both narrowed import groups are inside the former Mathlib umbrella. The ordinary arithmetic, symmetric-function and analytic proof architecture from the prior dependency audit is preserved. No axiom, `sorry`, native proof shortcut, target shadowing, new class premise, or circular transcendence assumption was added.

| File | Upstream SHA256 | Reviewed local SHA256 |
|---|---|---|
| `ETranscendental.lean` | `7cf361e9979a0b68e932a6105c89a0e74bed28d4d3070ac947b370c681942ef0` | `7cf361e9979a0b68e932a6105c89a0e74bed28d4d3070ac947b370c681942ef0` |
| `PiLindemann.lean` | `d7a7e51ecfa31365cf163558536e3702bc6b60d6984fa8bf6560dfc8fb07e030` | `d7a7e51ecfa31365cf163558536e3702bc6b60d6984fa8bf6560dfc8fb07e030` |
| `HermiteLindemann.lean` | `bd754566761fe4e7b34441420962d2d5d1d1c5a409ebca41e9346f55258df108` | `bd754566761fe4e7b34441420962d2d5d1d1c5a409ebca41e9346f55258df108` |
| `MonicRootSums.lean` | `c6b20c3138f3ec57e96de603f796422479894f42bbd45d2ebafd0d8ec8558d04` | `cad726aa56114f33a80a75bafba9fbe87d7a30e9da2dfff1d43efc482f40555c` |
| `SubsetSumEsymm.lean` | `311a97ce3b745500f3f14ff879c2eaa42299c5ab57914bf1c86fe04a6cdf3165` | `b9196dc2dc307cd7c9d32f703dab028c7bfecf2c036745c105b81581ba01503f` |
| `PiTranscendental.lean` | `7ffa9e9a3734edce153443ced0a144515ab539091634dc9ab497066873aefdb6` | `7ffa9e9a3734edce153443ced0a144515ab539091634dc9ab497066873aefdb6` |

## Exact project bridge

`MF21Restart/PiTranscendence.lean:12–13` states `MF21Restart.pi_transcendental : Transcendental ℚ Real.pi` and directly uses `LeanFormalizations.Transcendence.transcendental_pi_axiomClean`. It has no explicit or section-level hypotheses, target-changing definitions, or local notation. The imported capstone was already checked for the actual ordinary Mathlib transcendence predicate and real π, and its source is byte-identical upstream. This is exactly the classical transcendence ingredient needed at the end of unchanged manuscript Section 5. It is not the final trace-irrationality argument or a proof of MF-21 Target.

Bridge SHA256: `63978695081b2c4e863609090b0ae358470ae7e64e17893385237339d8315cc9`. The upstream Apache-2.0 license, immutable hash manifest, and source provenance comments remain present in `vendor/gotrevor-pi/` and the source headers; the new port comparison documents local differences separately. Earlier comments claiming upstream verification are not used as local check evidence.

## Actual local evidence and limits

The original run record `evidence/vendor-runs/20260920T190739652073Z/record.json` records successful compilation of the first three unchanged modules and the subsequent failed broad-import MonicRootSums attempt. That record correctly has `passed: false`; it is not presented as a successful whole-closure run. The coordinator separately reported MonicRootSums02, SubsetSum03, vendor-pi01 and pi-transcendence01 with exit 0 for the reviewed local hashes. I read their corresponding logs. The first six successful logs below are empty; the final bridge log prints the standard three axioms. An empty log is not independently treated as proof of a zero exit code; exit status comes from the record or coordinator's actual execution report.

| Successful local log | SHA256 |
|---|---|
| `evidence/vendor-runs/20260920T190739652073Z/ETranscendental.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `evidence/vendor-runs/20260920T190739652073Z/PiLindemann.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `evidence/vendor-runs/20260920T190739652073Z/HermiteLindemann.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `evidence/logs/vendor-monic-02.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `evidence/logs/vendor-subsetsum-03.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `evidence/logs/vendor-pi-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `evidence/logs/pi-transcendence-01.log` | `c00ffff999ca9d88dfc878252adff412287d06571644639a9d5899a87b38c91e` |

A later final source/pin-stable whole-project record remains the coordinator's responsibility. It must retain the successful optimized source hashes and prior failure history. No pending check, unrelated project declaration, full MF-21 target, or GitHub Comparator result is accepted by this report.
