# Fourier stencil and Laurent identity — independent review

Verdict: **APPROVE** for the six named scalar/matrix-entry ingredients below. No material source-fidelity or mathematical correctness issue found. This review does not approve a spectral recurrence bridge, circulant diagonalization/interlacing, determinant formula, or the complete MF-21 target.

Scope: independent statement/proof source review under the pinned REFEREE_STANDARDS, principally source fidelity and correctness, with finite-sum trust and computational-scope checks. The reviewer ran no Lean compiler, Lake build, Comparator, or GitHub check. The coordinator reported serial local runs `fourier-stencil-02` and `fourier-laurent-02` with exit 0 against the frozen hashes below; I read their logs, which print only `[propext, Classical.choice, Quot.sound]` for all six public declarations. The stencil log also contains tactic/linter messages; these do not alter the reported exit status or source-fidelity result. No Comparator evidence exists for these ingredients in this review.

## Exact source correspondence

`Definitions.lean:18–25` still defines the published sine-power symbol, normalized cosine Fourier integral, and Toeplitz entry at the integer difference of indices. `StatementBridges.complex_fourier_eq_cosine` (lines 44–65, separately reviewed unchanged source) proves equality to the published complex Fourier integral with negative exponential sign. Thus this review concerns actual coefficients, not an arbitrary family assumed to obey a recurrence.

`FourierStencil.symbol_eq_cosine_power` (lines 28–36) proves equality to `(2 - 2 cos θ)^m`, including m=0 and all real θ. This identifies the original manuscript's Section 1 symbol and the original problem's sine-power form. It introduces no domain restriction or nonvanishing assumption.

`fourierCoeff_succ` (lines 45–77) proves the correct coefficient convolution: center coefficient twice, minus each adjacent integer frequency. The identity uses the product-to-sum cosine formula, preserves normalization, and discharges continuity/integrability before splitting integrals. The frequency casts are signed integer-to-real casts, so negative frequencies are handled correctly.

`fourierCoeff_zero` (lines 88–94) proves the correct normalized zeroth symbol: 1 at k=0 and 0 at all other integer k. Its proof uses π nonzero only for the legitimate normalization division. `fourierCoeff_support` (lines 98–118) establishes vanishing for |k|>m by induction and the triangle inequality. The support is inclusive at ±m; no endpoint coefficient is discarded. `toeplitz_entry_eq_zero_of_lt_abs` (lines 121–124) applies that exact result to the actual finite matrix entries. Its statement correctly claims half-bandwidth **at most** m; nonvanishing of the extreme stencil entries is a distinct later result.

`FourierLaurent.fourierCoeff_laurent_sum` (lines 107–118) has exactly the statement locked in both Fourier statement documents: integer exponents, inclusive interval [-m,m], the same concrete coefficients, and every nonzero complex z. Its right side is `(2 - z - z⁻¹)^m`, exactly the Laurent polynomial used at manuscript line 142 before (13). This also supplies the scalar symbol identity needed for the circulant step at manuscript line 259. Neither of those later matrix constructions is proved by this scalar identity alone.

## Proof and edge-case checks

The Laurent proof first converts the established coefficient support bound into finite support (lines 16–29). In the induction step, all three functions in the subtraction have explicit finite-support proofs (lines 56–80). Both uses of finite-sum subtraction (lines 98–103) consume those proofs. Reindexing is the actual bijection k↦k-r on ℤ; the multiplier is z^r, and `zpow_add₀ hz` is applied with the necessary nonzero hypothesis. The public conclusion replaces the totalized finite-support sum with the ordinary displayed finite sum using a proved support inclusion (lines 111–118). No convergence assumption is omitted, and no infinite-support totalization makes the result vacuous.

Mathematical edge checks agree with these types: m=0 gives the singleton coefficient 1; m=1 gives coefficients -1,2,-1 and Laurent polynomial 2-z-z⁻¹; m=2 gives 1,-4,6,-4,1. The nonzero-z hypothesis is substantive in the general theorem: with Lean's totalized powers, m=2 and z=0 would give 6 on the left and 4 on the right. The statements are valid at orders below the manuscript's m≥3 and hence are useful generalizations, not weakened approximations to the target. Empty matrices introduce no unwanted spectral assertion.

There are no added hypotheses resembling a desired coefficient recurrence, expansion, spectrum, or Target; no legacy module import; no custom axiom or proof placeholder. The proof is symbolic integration, finite algebra, and induction. It needs no LeanCert numerical certification or brute-force enumeration. Existing Mathlib integral, trigonometric, finite-support, and integer-power APIs are reused.

The actual public theorem types match the locks in `FOURIER_STENCIL_STATEMENTS.md` and `FOURIER_LAURENT_STATEMENTS.md`. Provenance documentation accurately identifies the adapted legacy scalar strategy and its new proved symbol bridge. Optional tactic/linter cleanup is not a material issue and is unnecessary for this approval.

## Frozen evidence

The coordinator confirmed both proof-source hashes were frozen during this review. No source file was edited by this reviewer.

| File | SHA256 |
|---|---|
| `MF21Restart/FourierStencil.lean` | `c7c94724b95fffb35abf8f682a921a0badcca1de19e41b99b0502cd9349cf809` |
| `MF21Restart/FourierLaurent.lean` | `ffa0cb9a4f88ba83f76d5101875fc9e8065bbc3c7e582e0808be6bc939c69dad` |
| `FOURIER_STENCIL_STATEMENTS.md` | `143e36f8d3a7c067db8b70d3ed6945cbfedde65efc6c9db113f48f2a4415726c` |
| `FOURIER_LAURENT_STATEMENTS.md` | `48fdda3b0bcac23d9c19c4f37808b31a6bbec7ec88521eb98f098604d43807cd` |
| `MF21Restart/Definitions.lean` | `35a74047a81a9b7526e9bf039880ca8f07ae33314e2b5b960ab254e02fca4b51` |
| `MF21Restart/StatementBridges.lean` | `90992b2cf34bbbefdf9da9c04b814a693faba7ec8d48b16bdf8d00948c4db057` |
| `original-proof/solution.md` | `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa` |
| `reviews/REFEREE_STANDARDS.md` | `e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1` |
| `evidence/logs/fourier-stencil-02.log` | `20909b6cbd4993b66f0468d906f592ecce4e6f461b870c9f5a6c9a4b0589cbc1` |
| `evidence/logs/fourier-laurent-02.log` | `34161079f0535e916001c8559da7f8e76b0350742f3e503aeea367e2de94b7a2` |
