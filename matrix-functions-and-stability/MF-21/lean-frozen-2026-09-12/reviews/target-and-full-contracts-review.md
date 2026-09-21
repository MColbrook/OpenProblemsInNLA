# Independent review: complete Target assembly and exact contracts

Verdict: **APPROVE** for the TargetProof assembly, unchanged target fidelity, and seven-contract design at the exact hashes below. No material mathematical or contract defect remains in this scope. Reviewer: `mf21_restart_lean_audit`. The reviewer did not author TargetProof, Challenge, Solution, or their statement locks, and ran no Lean compiler. This is independent source review and independent inspection of the coordinator's actual local evidence. It is not a Comparator run or independent kernel replay.

The review follows the pinned `REFEREE_STANDARDS.md`, SHA256 `e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Exact original statement

The canonical README, SHA256 `1aac38ed3c7a83dfc3dddb4beeec26fcf117f23f5789b2a374c1332ba4cf359f`, and manuscript Theorem 1, SHA256 `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`, were read against Definitions and the final contract. Neither original source was edited by this review.

- `Definitions.lean:18–25` uses the actual symbol and integral-defined Toeplitz matrix. The row/column coordinates `Fin n` are zero based, but their difference agrees with the difference of the manuscript's indices `1,...,n`. The separate configured `complex_fourier_eq_cosine` contract retains the original complex integral, negative exponential sign, normalization, and every signed integer frequency. Its proved source is `StatementBridges.lean:44`.
- `Definitions.lean:38–49` sorts the complete eigenvalue multiset, retains multiplicities, and maps the published index `j` to position `j-1`. Thus `j=1` is the smallest and `j=n` is the largest eigenvalue. The artificial value outside `1≤j≤n` is unused in Target.
- `Definitions.lean:55–71` retains the exact mesh `jπ/(n+2)`, every term `k=0,...,p`, the required powers, constants independent of `n,j`, and the literal ceiling of `log(n+2)^2`. The additional positive-index guard in BulkBound is redundant by the configured `bulk_cutoff_pos` theorem, including small `n`.
- `Definitions.lean:75–80` quantifies over every natural `m≥3` and chooses one coefficient family before all three assertions. Restricting that family to `k≤2m` gives precisely the finite family requested by the canonical statement. Constants and thresholds may depend on `m,p`. The negated UniformBound is the actual critical-order all-index estimate, not failure for a different coefficient family.
- `TargetProof.lean:48–53` explicitly strengthens regularity to `ContDiffAt ℝ ∞` at every point of `[0,π]`. In this Mathlib pin `∞` denotes smooth order and is distinct from analytic order `⊤`. `target_proved` at lines 82–87 obtains continuity from this same smooth family; it does not reconstruct unrelated coefficients.

The unchanged Definitions SHA256 is `35a74047a81a9b7526e9bf039880ca8f07ae33314e2b5b960ab254e02fca4b51`.

## Assembly proof and the earlier failure modes

`TargetProof.lean:54–78` chooses exactly one actual implicit phase `Y` from `manuscript_implicit_taylor_with_spectral_error`. Its coefficient family is the exact derivative-defined `implicitPhaseCoefficient m Y`. The actual uniform Taylor estimates, vanishing orders, zero-order identity, and spectral comparison all concern this same `Y`.

The spectral error extracted at lines 60–66 is exactly `Cs*h^(2m)*j^(2m-1)*exp(-c*j)`, and is used only for `n≥N` and `j≥J`. No all-index critical exponential estimate is assumed. The Taylor error is separately `O(h^(p+1))`, without an exponential factor. Lines 67–69 invoke the already reviewed expansion assembly, and discharge its finite-prefix eigenvalue premise with the proved actual `eigenvalue_fixed_prefix_bound`. The bulk estimate uses the original log-squared cutoff and the genuine scale gain. There is no unresolved lower-index premise in the final theorem.

The auxiliary obstruction at lines 22–44 is sound as a conditional statement about the already constructed phase, and all its construction hypotheses are discharged at lines 70–71. In particular:

1. `intro hU` at line 35 introduces the hypothetical critical UniformBound. Line 38 passes this exact hypothesis to `critical_bound_implies_actual_fixed_index_limit`. The hypothesis is essential; the contradiction is not derived from two limits already assumed in the theorem. That fixed-index result applies to every original `j≥1`, retains the entire order-`2m` Taylor sum, and handles `j` below the high-index cutoff using IFT displacement.
2. Lines 39–40 discharge the spectral trace passage's actual summable-majorant premise with `eigenvalue_eventual_reciprocal_tail_bound`. The majorant is only required for `j≥2`; the first term is handled in the separately reviewed passage by its positive fixed-index limit.
3. Lines 41–42 compare limits of exactly the same sequence, `(1/(n+2))^(2m) * trace (toeplitz m n)⁻¹`. `ActualTraceLimit.toeplitz_inverse_trace_tendsto_mesh` proves the rational limit of that actual sequence; it is not an added assumption or a different `n` normalization. `SpectralTracePassage` gives the series with original index `j=k+1`, so no first eigenvalue is dropped.
4. Lines 43–44 use the proved rationality of the kernel constant and the proved irrationality of the exact normalized series for `m≥3`. Both parity branches retain the positive rational correction. The π-transcendence result is a proved local port, not a custom axiom.

Consequently `MF21Restart.target_proved : Target` has no extra spectral, root-list, coefficient, interlacing, inverse-kernel, trace-limit, or transcendence hypothesis. The completed assembly supplies the original target rather than another generic implication.

The auxiliary results were independently reviewed in `actual-fixed-index-review.md`, `spectral-trace-passage-review.md`, `expansion-assembly-review.md`, `implicit-spectral-error-review.md`, and the earlier trace-series/π reviews. The coordinator's actual inverse-kernel/trace chain has the other referee's separate review. This report does **not** independently re-review dependencies authored by this reviewer: the circulant/interlacing chain, BulkDecay, PhaseQuantitative, OrderedTailCounting/PhaseWindowIndexing, and the earlier Fourier, root-list, recurrence, phase-product, weighted-factorization, and boundary-error components. Their independent review belongs to the coordinator/other referee. In particular, inspecting successful CirculantBounds evidence below is not an independent proof review of this reviewer's own source. The four final CirculantOrder/DiagonalInterlacing/HermitianInterlacing/CirculantBounds sources have the other referee's separate **APPROVE** in `circulant-interlacing-bounds-referee-b.md`, SHA256 `442b891f43e5feba994f1c2c47adc56c93bf7f08c7f426598af735bb8c4d2496`, covering all 14 source-matched standard-axiom reports; its exclusions remain in force.

## Exact Comparator boundary

All seven theorem signatures in `Challenge.lean` and `Solution.lean` agree textually after whitespace normalization. Their fully qualified names agree exactly with `comparator.json`. The two new complete contracts are:

- `MF21Restart.Contracts.manuscript_smooth_target`, with the explicit smoothness and all three properties of one family;
- `MF21Restart.Contracts.target_proved : MF21Restart.Target`, with no assumptions.

The five prior component contracts remain configured unchanged. There are no definition holes or extra permitted axioms. The permitted list is exactly `propext`, `Classical.choice`, and `Quot.sound`.

Challenge's local import closure contains only `Challenge` and the unchanged `MF21Restart.Definitions`. Its other direct/imported boundary modules are Mathlib's matrix spectrum, trigonometric sinc, interval-integral basics, and ContDiff definitions. It imports no proof module. Solution imports the proof root and never imports Challenge. A comment-stripped scan of Solution's 123-module local closure and TargetProof's 116-module local closure found no `sorry`, `admit`, custom `axiom`, `unsafe`, `native_decide`, `implemented_by`, or `extern`. Challenge has exactly seven deliberate theorem placeholders, at lines 20, 24, 40, 48, 51, 59, and 62; these are outside the proof closure. This lexical check is supplementary to the actual axiom reports, not a substitute for them.

One preflight issue was identified and resolved: Audit initially printed the two new `Contracts` names while importing only the proof root. The coordinator changed its import to `Solution`. Current `Audit.lean`, SHA256 `8c3cbee5e8ac2510753fac28633be96c39c24cad70c0f12ebdcdeb89dece35d1`, imports Solution and not Challenge, and its actual preflight produced all 386 expected, uniquely named reports with only permitted axioms. A failed earlier root import-order test is retained and is not counted as successful evidence.

## Exact versions and actual local evidence

| Source / statement / configuration | SHA256 |
|---|---|
| `MF21Restart/TargetProof.lean` | `189eb2e1ed8ad943d78c982e36203cae995e0c6b731293161cb615c9228edf53` |
| `TARGET_ASSEMBLY_STATEMENTS.md` | `466dc09381e2b2fdcec3cae8883be07b1c09de815d4be4076b18d07313c0df80` |
| `COMPARATOR_TARGET_STATEMENTS.md` | `a1c87983730695ca19aa94e328909a3f94ac43a8ce3f9630b0f1cecd42f05774` |
| `Challenge.lean` | `9bb51fae68bab7a4ba5ff8fe7c3b815e361f31c041897ee04596dfd0215989b2` |
| `Solution.lean` | `97dffa0a35b7067b784763adcdf01c21f8da7d005a69c32662dbe9c84e080659` |
| `comparator.json` | `dabddad03ffd9e58d22f1712583ee686d166ede59ebe073798fddd57a928c3ab` |
| `MF21Restart.lean` | `6e12186336a3799391b8b6b1cb872250ef1f4e19d2062c32d25258ad59e23a7d` |
| Archived full-run `evidence/runs/20260921T000301098707Z/verify_local.py` | `fddada659794fdf62748ffc0790368c30b1bf66ff0acc939161edbd1fd4b8d85` |

The reviewer recomputed all source/log/output hashes in the successful records below. Every current source, retained log, and built output matches its record; each has exit code 0 and `source_unchanged: true`. Commands are the recorded `lake env lean -j1 -M4096 -o ...` calls with `LEAN_NUM_THREADS=1`.

| Record | Record SHA256 | Log SHA256 | Output SHA256 |
|---|---|---|---|
| `target-proof-01.json` | `0a929a64baa4ad3b48fc1971b9a21163acd48c8c6c152a0a7c22705a298da22a` | `737966cd140b3e3904bec238d0604342c486e44f4986f962e9c24e70233d8732` | `0a6f9ba97b2bab4f7ce59a65ffbcbd5164b974d437c39525242706158862dab5` |
| `full-root-02.json` | `50eff8b0c12277226a7f50f1b2602f6c1e8c4b81bcdba151520b3ba38229fcfc` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | `859e6e178cfc775cddab058000495964cb8364aa6f290a3aef26bf8dac9a8b84` |
| `full-solution-01.json` | `33cd263701ad5429b430c017e1c6f58c0779a6c307e4901901bfc5f43d056f8a` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | `e8f01207600d9c6340e5728635ae6d10ecb7cc96246222bead315effcc73e4b5` |
| `full-challenge-01.json` | `32b5e8aee3e3cf6679aae88cc4273e78ddfce3bb0f35bb01fc7859985088649d` | `e061da0f14deab97d9ad389111822916cd5ca5e68ea9be0024b4be7b7dfbeee1` | `31c09c3ea045eb7a9df07a54e330f700be5035bf1e9b9aea7fba30f90d231bb1` |
| `full-audit-01.json` | `5f859db3a41731c292484ac904f9ba91701a49e81e953bf5a3a7b7d5312855b1` | `a1e73e7919dc4a8877bf5e2814c9b225c8781739818459a6170f50d7d646d098` | `02a9579b67ba0b9fecd47ebf25879bbb82cc56846eafed5319e2074a7013cab0` |

These records are under `evidence/logs/`. TargetProof's three explicit reports cover `implicitPhase_critical_bound_impossible`, `manuscript_smooth_target`, and `target_proved`; each contains only the three permitted standard axioms. The full audit also reports the two complete contract wrappers with the same axioms. Challenge's seven expected `sorry` warnings are deliberately excluded from proof-side trust claims.

For the dependency evidence only, CirculantBounds02 has source SHA256 `f63c776c46312d11347199ae3eb42003725dd95c578012b72f490fbb9a2a86ff`, record `c15e7b6ebab87bb9c84ddc9c7aa02985804e8ef45d00e6e817b7610d62b41cbf`, log `8dfa147e85fdff460c368737f751a26052635b6d0b376c8a47e4d0a38e8725cd`, and output `347d4c86ecf65795898fd3cf4ac3ab3e766e873410e3ad45071b57931e3c4077`. All six reports are standard-only. As stated above, this is not an independent review of that source.

The pinned toolchain is Lean 4.33.1; Mathlib is `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert is `621a43d7cf21f87872392a01e874f2f1dbddc926`. The existing kernel-mode numerical certificate and six-file π proof port retain their separate reviewed scopes and attribution. They introduce no additional axiom into the actual target reports.

## Verification limits

The complete target has an actual source-matched successful **local** Lean proof and standard-axiom reports. The subsequent complete 125-source integrated run also passed: `evidence/runs/20260921T000301098707Z/record.json`, SHA256 `abdf520ffbcfc2fe80236e0c303795d97a50e8c11f46a5edbac8a29dba5d7856`, started at `2026-09-21T00:03:01.098707+00:00` and finished at `2026-09-21T00:18:29.089795+00:00`. The reviewer independently recomputed every recorded source, dependency-configuration, log, and compiled-output hash; checked that all 125 exits were zero; and matched all 386 actual axiom reports exactly to Audit's unique declaration list. Every report contains only permitted standard axioms. The frozen manuscript hash and `latest-local.json` byte equality with the immutable record were also checked. No mismatch was found. This was inspection of the coordinator's run, not a second compiler run by the reviewer.

The exact runner used for that proof run is archived in its run directory at the hash in the table. A later portability-only lock-path edit to the current runner has separate Python smoke evidence in `evidence/runner-portability-smoke.json`; it changed no Lean source or compilation command. The complete Lean run used the archived runner. The portability edit and its tests were authored by this reviewer and are not claimed as independently reviewed here.

Static signature equality and successful local compilation are not a real Comparator comparison. No GitHub non-root Linux Comparator/sandbox/kernel run has occurred for this restart, and this report does not increase the completed-verification count. Final metadata is reviewed separately in `metadata-final-review.md`. Exact later GitHub evidence must be recorded separately.
