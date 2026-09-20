# Provenance and verification of the pi-transcendence input

The six Lean source files in this directory are adapted from Trevor Morris's
[lean-formalizations repository](https://github.com/gotrevor/lean-formalizations/tree/3a24a73416f83c32b4d4a2ac09588524c6291650/src/LeanFormalizations/NumberTheory/Transcendence),
commit `3a24a73416f83c32b4d4a2ac09588524c6291650`, under the accompanying
Apache-2.0 [LICENSE](LICENSE). Original AI-assistance disclosures and theorem
provenance are retained in the source comments. The original repository
targets Lean/mathlib v4.31.0. This copy has been checked with Lean 4.33.1 and
mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The dependency chain closes the Lindemann proof at the actual real constant
`Real.pi`; it does not introduce transcendence as an axiom or hypothesis.
The file `PiTranscendental.lean` assembles the earlier analytic approximation
theorem, integer nonvanishing, conjugate-polynomial construction, and
symmetric-polynomial lemmas. Its exact conclusion is
`Transcendental ℚ Real.pi`.

Changes from the upstream snapshot are limited to local import prefixes and
one compatibility fix: explicitly supplying
`Multiset.powersetCard_zero_right` in the empty/successor case of
`ringHom_map_multiset_esymm`. No mathematical statement was altered.
Original and adapted SHA-256 hashes are recorded in
[provenance.json](provenance.json).

The canonical project replay and Linux Comparator check the complete imported
proof closure, including all six files. See the project [reproduction
instructions](../../README.md). The original development receipts remain in
the dated review directory; they are historical component checks, not the
canonical acceptance record.

The source was located through the public
[mathlib documentation PR #43144](https://github.com/leanprover-community/mathlib4/pull/43144).
The alternative [mathlib Lindemann–Weierstrass PR #28013](https://github.com/leanprover-community/mathlib4/pull/28013)
was also inspected at commit `5a0057ccc26b13a4e361f503f5f765bf56a8d353`;
it needs newer supporting mathlib modules and was not imported here.

`MF21TraceSeries.lean` also proves the exact shifted-series evaluations and
the irrationality of the actual model trace for every integer `m ≥ 3`, with
no rationality, tail-evaluation, or transcendence hypotheses.

`FiniteTraceObstruction.lean` proves the abstract eventual finite-head
separation and its transfer to the original remainder scale.
`ActualTraceObstruction.lean` instantiates every premise with the actual
Toeplitz spectrum, direct inverse-trace limit, summable majorant and common
coefficient-family limit. `FinalTarget.lean` assembles the full MF-21 result.

This directory supplies the arithmetic input. Full-project verification and
independent semantic review are recorded separately; no acceptance is
inferred solely from a successful component build.
