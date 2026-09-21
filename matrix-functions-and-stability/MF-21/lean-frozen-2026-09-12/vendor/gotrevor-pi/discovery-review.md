# MF-21 π-transcendence dependency audit — 20 September 2026

Verdict: **APPROVE the gotrevor source as a concrete candidate for a local port and verification attempt.** This is a source/import/statement audit, not acceptance of an already checked proof. I ran no Lean, Lake, Comparator, or GitHub workflow; no external artifact was executed. The requested theorem must still pass the coordinator's pinned local Lean build and an actual axiom audit before use in MF-21. Complete MF-21 verification remains open.

## Exact smaller candidate

Repository `gotrevor/lean-formalizations`, immutable commit `3a24a73416f83c32b4d4a2ac09588524c6291650`. The actual [capstone source](https://github.com/gotrevor/lean-formalizations/blob/3a24a73416f83c32b4d4a2ac09588524c6291650/src/LeanFormalizations/NumberTheory/Transcendence/PiTranscendental.lean#L24) states the unconditional ordinary Mathlib target:

`LeanFormalizations.Transcendence.transcendental_pi_axiomClean : Transcendental ℚ Real.pi`.

There are no section parameters or hypotheses. The six local files declare only theorems/lemmas in `LeanFormalizations.Transcendence` and its subnamespace; they introduce no custom definition, instance or notation that replaces `Transcendental`, ℚ, ℝ, or `Real.pi`. The final proof supplies the symmetric-function hypothesis of `transcendental_pi_of_subsetSumEsymm` with `subsetSum_esymm_rational`. The former assumes algebraicity of π only inside its contradiction proof, then uses the minimal polynomial of iπ and the ordinary Euler identity. This matches the transcendence dependency used in the unchanged manuscript, without a transcendence premise.

The proof's analytic engine `PiLindemann.no_intPoly_exp_relation` (lines 155–254) invokes the proved Mathlib `LindemannWeierstrass.exp_polynomial_approx`, selects a sufficiently large prime, and constructs an integer both zero by a norm bound and nonzero by divisibility. `MonicRootSums` supplies the polynomial root-sum integrality premise via Vieta/Newton identities. `SubsetSumEsymm` supplies rational symmetric functions via the fundamental theorem of symmetric polynomials. These are genuine proof bodies, not declared assumptions. The historical Hermite–Lindemann axiom mentioned in comments has been removed from the actual file, which now contains only the real-to-complex algebraicity transport helper. I checked this architecture and the key actual statements; I have not independently reconstructed every tactic proof in the closure.

## Complete source closure and fetch contract

Exactly six local Lean files, 69,944 bytes / 1,218 lines, plus the root license. All other imports are Mathlib. The repository's unrelated `PrimeNumberTheoremAnd` dependency is not in this closure. Preserve these module names when vendoring; do not import the repository umbrella or its comparator/WIP libraries.

Topological compile order:

1. `LeanFormalizations.NumberTheory.Transcendence.ETranscendental`
2. `LeanFormalizations.NumberTheory.Transcendence.PiLindemann`
3. `LeanFormalizations.NumberTheory.Transcendence.HermiteLindemann`
4. `LeanFormalizations.NumberTheory.Transcendence.MonicRootSums`
5. `LeanFormalizations.NumberTheory.Transcendence.SubsetSumEsymm`
6. `LeanFormalizations.NumberTheory.Transcendence.PiTranscendental`

All sources reside under `src/LeanFormalizations/NumberTheory/Transcendence/` upstream. The exact raw URL pattern is `https://raw.githubusercontent.com/gotrevor/lean-formalizations/3a24a73416f83c32b4d4a2ac09588524c6291650/src/LeanFormalizations/NumberTheory/Transcendence/FILE.lean`. GitHub's equivalent Contents API is `https://api.github.com/repos/gotrevor/lean-formalizations/contents/src/LeanFormalizations/NumberTheory/Transcendence/FILE.lean?ref=3a24a73416f83c32b4d4a2ac09588524c6291650`. No branch name is needed for reproducible fetches.

| File | Bytes | SHA256 |
|---|---:|---|
| `ETranscendental.lean` | 17168 | `7cf361e9979a0b68e932a6105c89a0e74bed28d4d3070ac947b370c681942ef0` |
| `PiLindemann.lean` | 28247 | `d7a7e51ecfa31365cf163558536e3702bc6b60d6984fa8bf6560dfc8fb07e030` |
| `HermiteLindemann.lean` | 1450 | `bd754566761fe4e7b34441420962d2d5d1d1c5a409ebca41e9346f55258df108` |
| `MonicRootSums.lean` | 12908 | `c6b20c3138f3ec57e96de603f796422479894f42bbd45d2ebafd0d8ec8558d04` |
| `SubsetSumEsymm.lean` | 8587 | `311a97ce3b745500f3f14ff879c2eaa42299c5ab57914bf1c86fe04a6cdf3165` |
| `PiTranscendental.lean` | 1584 | `7ffa9e9a3734edce153443ced0a144515ab539091634dc9ab497066873aefdb6` |

Machine-readable exact URLs, hashes, local download paths, destination module paths, and compile order are in [gotrevor-vendor-manifest.json](./gotrevor-vendor-manifest.json). The already downloaded files are under `/private/tmp/mf21-pi-dependency/gotrevor/src/`; copying them after checking these hashes avoids further downloads. License: `/private/tmp/mf21-pi-dependency/gotrevor/LICENSE`, SHA256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`.

The pinned repository [LICENSE](https://github.com/gotrevor/lean-formalizations/blob/3a24a73416f83c32b4d4a2ac09588524c6291650/LICENSE) is Apache-2.0. Commit-pinned Contents API listings of every ancestor directory found only the root LICENSE and no nested license, copyright, or NOTICE file. Preserve this license and the source provenance comments, including their attribution to Harmonic Aristotle for the two symmetric-function developments. This is a record of the repository's stated terms, not a claim to have audited third-party provenance beyond the supplied files.

## Static checks and outstanding trust boundary

An explicitly comment/string-stripped scan of all six files found no `axiom`, `sorry`, `admit`, `unsafe`, `partial`, `run_tac`, `native_decide`, `implemented_by`, `elab`, `macro`, `syntax`, or `initialize` code token. All source hashes matched the download manifest. All external import paths exist at destination Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. Results are retained in [gotrevor-static-audit.json](./gotrevor-static-audit.json).

Upstream pins Lean/Mathlib 4.31.0; the MF-21 project pins Lean 4.33.1. Existing paths establish only import-path availability, not elaboration/API compatibility. Two files use umbrella `import Mathlib`, which may add load cost under the 4096 MiB compiler budget. No local build, kernel check, axiom footprint, or runtime-resource result has been observed for these exact sources on the destination pin. Upstream comments and [PR 43144](https://github.com/leanprover-community/mathlib4/pull/43144) claim standard axioms; those claims are not substituted for checks here. The retrieved PR is open, unmerged, and changes only the external-proof listing in `docs/100.yaml`, with zero Lean declarations. It is not a Mathlib proof acceptance or a destination-version compatibility result.

The coordinator can now vendor exactly the six files and license, run its normal serial local build, and audit the full type and `#print axioms` of the capstone. If any port edits are needed, preserve the original source hashes and record the patched file hashes and actual results separately. No custom axiom is needed or authorized as a port workaround.

## Omega comparison

Repository `RamzesX/Omega-Theory-Discrete-Spacetime`, immutable commit `4d1b7efc41b52049f90b61613ef9f8196572611b`, source root `PhysicsPapers/LeanFormalizationV2`, pins Lean/Mathlib 4.29.0. Its actual [direct capstone](https://github.com/RamzesX/Omega-Theory-Discrete-Spacetime/blob/4d1b7efc41b52049f90b61613ef9f8196572611b/PhysicsPapers/LeanFormalizationV2/OmegaTheory/Irrationality/CustomMath/LindemannPremiseRatProofPiTranscendentalUnconditionalReal.lean#L53) also has unconditional type `Transcendental ℚ (Real.pi : ℝ)`. It composes a high-degree bridge discharge, a low-degree reduction, and a conditional transcendence assembly. The bridge is an explicit polynomial/exponential-sum property, and the discharge provides actual witnesses; it is not defined as `True`.

The direct capstone's exact local import closure has 49 files / 324,499 bytes / 7,282 lines, with only Mathlib external imports. Importing `PiStratum` instead adds two unnecessary files. All external import paths exist in the destination pin. The same stripped keyword scan found no forbidden proof placeholder or unsafe token in the direct closure. Several older imported progress-marker definitions are `Prop := True`; they do not change the capstone's ordinary mathematical statement. This observation is not a complete semantic review of its 7,282-line proof graph. The larger and older closure creates substantially more porting work than the six-file candidate.

Its pinned root [LICENSE](https://github.com/RamzesX/Omega-Theory-Discrete-Spacetime/blob/4d1b7efc41b52049f90b61613ef9f8196572611b/LICENSE) is GPL-3.0; no separate license was returned at `PhysicsPapers/LeanFormalizationV2/LICENSE`. README/paper claims are not kernel evidence or a substitute for applicable source terms. This candidate was inspected for comparison, not selected for vendoring. Full file hashes/import order and static findings are in [omega-static-audit.json](./omega-static-audit.json). Neither candidate was compiled by this reviewer.
