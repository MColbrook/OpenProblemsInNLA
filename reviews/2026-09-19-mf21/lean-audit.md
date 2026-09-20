# MF-21 Lean audit — 19 September 2026

**Full MF-21 verification is incomplete.** No theorem proves `MF21Challenge.FullTarget` or `MF21Challenge.UniversalObstruction`. The material below is a proposed statement boundary and seven supporting theorems, plus the elementary symmetry theorem used to define actual matrix eigenvalues. It must not be described as a Lean verification of the original Toeplitz conjecture, and it does not justify a catalog status change.

This is work by a Codex AI agent. The repository's `AGENTS.md`, `CONTRIBUTING.md` Lean section and `docs/lean/README.md` were read. The authoritative isolated Linux Comparator workflow was **not** run. No external human review is asserted.

## Source and dependency identity

The audit began against repository commit `de97a72364055bddb65f23d2da8566e0594b2a8c` and the following source bytes:

| Source | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-21/README.md` | `d7072f0d69da1db6eeb761517bec3bc63f59ba64ebb821caf5a5b7a5609c90a0` |
| `matrix-functions-and-stability/MF-21/solution.md` | `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa` |
| `matrix-functions-and-stability/MF-21/solution.tex` | `1baff64e748b8a3a31d53f1727560937e5c84524a202a25bc92c081b4f1fcd49` |

The conjecture is attributed to Barrera–Böttcher–Grudsky–Maximenko, and the informal solution to George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. New audit Lean code was produced by a Codex AI agent and is not attributed to either set of mathematical authors.

Lean is `4.33.1`, native `arm64-apple-darwin24.6.0`, compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. Mathlib is pinned to `0df444a360eaa60ab8c11dca51a86af692955474`. The [Lake manifest](lean-development-source.tar.gz) pins transitive dependency revisions. The local replay reused already-compiled dependency artifacts and checked that Mathlib's tracked source files were clean at the expected commit. It did not freshly rebuild all dependencies from source.

## What was checked

[Challenge.lean](lean-development-source.tar.gz) defines:

- The exact symbol `(2 sin(theta/2))^(2m)`.
- The real symmetric matrix with entries `(-1)^d * choose(2m,m+d)`, where `d=|i-j|`. `Nat.choose` is zero outside the bandwidth. The equality with the source's Fourier-integral coefficients is still an explicit correspondence obligation.
- Actual eigenvalues from Mathlib's Hermitian spectral theorem. `eigenvalues₀` is antitone, so the index is reversed using `Fin.rev` to obtain increasing order with multiplicity. Lean index `j : Fin n` corresponds to source index `j.val+1`.
- The exact grid, natural-log-squared ceiling cutoff, continuous coefficient functions on `[0,pi]`, all orders `p≤2m−1`, constant and dimension quantifiers, one common coefficient family, and same-family obstruction.
- `FullTarget : Prop` for every `m≥3`, and the separate stronger `UniversalObstruction : Prop` excluding every continuous family. **Defining a proposition does not prove it.**

The only theorem in this file is `toeplitz_isHermitian`, proving the elementary symmetry needed to use the spectral definitions. Independent AI-agent statement reviews passed for SHA-256 `34835e10fc601004efc13530e3673056345d87bde23d5b176d8e302bf6c548cc`: [trace reviewer](challenge-statement-review.md) and [bulk reviewer](lean-statement-review.md). Both reviewed actual spectral definitions as well as the quantifiers. The proposed `FullTarget` captures the original continuous target; the manuscript's stronger smoothness assertion remains an additional proof obligation.

[CoefficientUniqueness.lean](lean-development-source.tar.gz) proves:

1. `coefficient_unique_of_weighted_bigO`: if `(a_n-b_n)h_n^k = O(h_n^(k+1))`, `h_n→0`, `h_n` is eventually nonzero, and `a_n→A`, `b_n→B`, then `A=B`.
2. `continuous_coefficient_unique`: the preceding result for continuous coefficients sampled along a convergent mesh.
3. `expansion_unique_on_mesh`: strong induction gives equality of the coefficient families when both finite expansions have the stated estimates at every truncation order on a convergent mesh contained in the domain.

These generic results do **not** instantiate the MF-21 mesh or eigenvalue estimates. Their continuity premise is `ContinuousAt`, including any endpoint in the domain, rather than the original `ContinuousOn`; one may apply them on the open interval and separately extend equality to endpoints, but that linkage is not formalized. The estimates through every truncation order are explicit hypotheses. Deriving them from a single top-order expansion using bounded higher coefficients is another remaining application step.

[TraceArithmetic.lean](lean-development-source.tar.gz) proves:

1. `rational_sub_div_pow_irrational`: for transcendental real `t`, rational `u,v` with `v≠0`, and `k>0`, `u-v/t^k` is irrational.
2. `trace_values_ne`: the rational and proposed spectral trace values differ, **given the explicit hypothesis `Transcendental ℚ Real.pi`**.
3. `trace_limits_inconsistent`: a sequence cannot converge to both of those values, with the two limits and pi transcendence supplied as hypotheses.
4. `zero_remainder_satisfies_both_orders`: the identically zero error satisfies both adjacent nonnegative power bounds. Thus an upper bound alone does not establish failure at the next order.

The pinned Mathlib contains only `NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean`; this audit found no theorem establishing transcendence of pi in that checkout. An unproved axiom was not introduced to hide this missing input.

## Execution and axiom evidence

The exact successful local command was:

```bash
python3 reviews/2026-09-19-mf21/lean/replay.py \
  --lean /private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean \
  --packages /private/tmp/nla-formalization-campaign-20260915/linear-systems-and-elimination/IE-15/lean/.lake/packages
```

The replay directly invokes Lean with `--trust=0` on all three source modules. That flag requests type checking of imported modules. It checks the compiler version, pinned Mathlib commit and clean tracked Mathlib source, saves source hashes and exit codes, and rejects unexpected or missing axiom reports. All three invocations exited `0`. All eight proved declarations list exactly the permitted foundational axioms `[propext, Classical.choice, Quot.sound]`; none reports `sorryAx`, a custom axiom, or native-execution trust.

Retained evidence: [result.json](lean-development-source.tar.gz), [trace arithmetic log](lean-development-source.tar.gz), [coefficient uniqueness log](lean-development-source.tar.gz), [statement typecheck log](lean-development-source.tar.gz). The Lake project includes all three modules as default targets; the **executed** workflow is the direct replay above, not a claimed fresh Lake build or Linux Comparator run.

The replay script can use another installed Lean `4.33.1` binary and an equivalent pinned compiled packages directory. With a populated local `.lake/packages`, it defaults to that cache. The absolute temporary paths above document the actual run and are not portable dependencies in the Lean source.

## Remaining obligations for full verification

| Obligation | Current formal status |
| --- | --- |
| Fourier coefficient equals the signed-binomial matrix entry | Not proved; statement correspondence requires this bridge |
| All eigenvalues in `(0,4^m)` and correctly matched to eigenangles | Not proved |
| Smooth stable roots, phase extension and phase endpoint values | Not proved |
| Exact recurrence/boundary determinant and normalized exponential remainder with derivative bound | Not proved |
| Top-down root indexing, simplicity and upper-endpoint cancellation | Not proved |
| Uniform implicit-function construction and Taylor coefficients with endpoint vanishing orders, including the manuscript's stronger smoothness assertion | Not proved |
| Uniform lower-order expansion and logarithmic-squared cutoff estimate | Not proved |
| Cauchy interlacing estimates supplying the trace tail domination | Not proved for this matrix family |
| Böttcher–Widom inverse-kernel limit, diagonal passage, beta integral and rational trace limit | Not proved |
| Fixed-index limit implied by a hypothetical top-order expansion | Not proved |
| Dominated convergence of inverse eigenvalue sums | Not proved for this eigenvalue family |
| Odd/even shifted zeta identities and their rational/nonzero finite corrections | Not proved |
| Transcendence of pi in the checked dependency environment | Explicit hypothesis of the arithmetic lemmas; not proved |
| Application of mesh uniqueness to the original continuous coefficient families | Generic helper proved; source-specific linkage not proved |
| `FullTarget` and the stronger all-family obstruction | Proposition definitions only; no proofs |
| Fresh isolated non-root Linux Comparator and required frozen statement/proof reviews | Not run for this partial project |

A successful partial replay cannot discharge these obligations. The correct current report is that a statement boundary and supporting components have been checked locally, while the requested complete Lean proof remains unfinished.
