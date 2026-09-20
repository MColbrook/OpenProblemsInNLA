# MF-21: exact statement and proof obligations

The permanent target is Conjecture 8.4 of Barrera, Böttcher, Grudsky and
Maximenko, *Eigenvalues of even very nice Toeplitz matrices can be unexpectedly
erratic*, arXiv:1710.05243, page 26. The canonical problem remains
[`../README.md`](../README.md); the revised manuscript is
[`../solution.md`](../solution.md).

There are no numerical certificates or experimental premises. Every matrix,
inequality, asymptotic estimate, series evaluation and transcendence input in
the exported proof is symbolic. The prescribed axiom set is a subset of
`propext`, `Classical.choice`, and `Quot.sound`. No `native_decide`, custom
axiom or proof-development placeholder is permitted.

## Trusted definitions and exact quantifiers

`MF21/Definitions.lean` fixes the following objects. It contains definitions
and the elementary Hermitian-symmetry proof; it imports no solution module.

| Informal object | Formal interpretation |
| --- | --- |
| Integer parameter | `m : ℕ`, with `3 ≤ m` in every full target |
| Symbol | `(2 * Real.sin (theta / 2)) ^ (2 * m)` |
| Matrix | Real `n` by `n` matrix, indices `Fin n`, signed binomial entry at `Nat.dist i.val j.val`; no periodic wraparound |
| Fourier convention | The selected Fourier bridge proves that each real matrix entry, cast to `ℂ`, is exactly `(2π)⁻¹ ∫[-π,π] g_m(θ) exp(-i(i-j)θ) dθ` |
| Eigenvalues | Mathlib's actual Hermitian eigenvalues, reversed by `Fin.rev` into increasing order, counted with multiplicity |
| Source index | Formal `j : Fin n` represents the source index `j.val + 1` |
| Grid | `(j.val + 1) * π / (n + 2)` |
| Cutoff | Natural ceiling of `(Real.log (n + 2))²`, compared with `j.val + 1` |
| Coefficients | One function `d : ℕ → ℝ → ℝ`, independent of `n` and `j`; only indices through `2m` enter the original target |
| Continuity | `ContinuousOn (d k) (Set.Icc 0 Real.pi)` for every `k ≤ 2*m`, including both endpoints |
| Uniform estimate | `∃ D > 0, ∃ N, ∀ n ≥ N, ∀ j : Fin n`, the stated absolute remainder bound |
| Lower orders | Every natural `p ≤ 2*m - 1`; each order has its own uniform constants |
| Highest bulk order | Order `2m`, remainder at most `D / (n+2)^(2m+1)`, for every source index above the exact cutoff |
| Same-family obstruction | The very same `d` does not satisfy the highest-order bound over all indices |
| Universal obstruction | Separately exported: no continuous family satisfies that all-index bound, without assuming its leading coefficient in advance |

The asymptotic quantifiers allow an arbitrary finite initial set of dimensions
to be discarded. The `n = 0` convention introduces no hypothesis about large
positive dimensions. No simplicity, diagonalizability, eigenangle existence,
trace convergence or coefficient-existence assumption is left in the final
targets.

## Stronger claims of the revised manuscript

The selected smooth common-family theorem uses the same `d` for all original
estimates, `d 0 = g_m` on the entire closed interval, smoothness at every point
of that interval, the obstruction, and the following sharpness statements:

- A fixed positive integer `J` and positive `eps` witness an error strictly
  larger than `eps / (n+2)^(2m)` at some `j.val < J`, for every sufficiently
  large `n`. The witnessing index may depend on `n`.
- A positive constant bounds the error for every index by a constant times
  `(n+2)^(-2m)` for every sufficiently large `n`.

These are the lower and upper maximum-error bounds in Corollary 6. They do
not claim a particular fixed index always attains the lower bound.

## Proof correspondence

| Manuscript step | Principal formal modules |
| --- | --- |
| Source Fourier matrix, positivity and actual spectrum | `FourierCoefficients`, `ToeplitzGram`, `SpectralTrace`, `Eigenangles` |
| Stable roots and endpoint desingularization, Lemma 2 | `BulkRoots`, `BulkEndpoint`, `BulkRootFamily`, `BulkPhase`, `BulkTotalPhase`, `BulkEta`, `BulkDecay` |
| Exact boundary criterion | `RecurrenceBasis`, `BoundaryPolynomial`, `BoundaryDeterminant`, `BoundarySpectrum`, `ActualBoundaryDeterminant` |
| Normalized determinant, Lemma 3 | `BoundaryNormalization`, `BoundaryExpansion`, `BoundaryDecay`, `BulkSlopes`, `BulkLeadingPhase`, `ActualBoundaryError`, `ActualBoundaryExpansion`, `BoundaryReality`, `ActualBoundaryPhase` |
| Derivative and upper-endpoint bounds | `ExponentialSums`, `PhaseRotatedError`, `RealBoundaryError`, `ActualBoundarySmooth`, `ActualBoundarySimplicity` |
| Simple roots, top-down indexing, Lemma 4 | `DeterminantSimpleKernel`, `SpectralSimplicity`, `PerturbedPhase`, `PhaseCellRoot`, `TopDownIndexing`, `PhaseIndexing`, `PhaseCutoffs`, `PhaseErrorEstimate`, `ActualPhaseIndexing`, `ActualTailAngles` |
| Circulant bounds (21)–(22) | `CompressionInterlacing`, `CirculantSpectrum`, `CirculantOrdering`, `SpectralBounds` |
| Common smooth coefficients and estimates (23)–(25) | `SmoothQuantization`, `UniformQuantization`, `UniformTaylor`, `QuantizationTaylor`, `FiniteHeadModel`, `SymbolTransfer`, `ExponentialCutoff`, `ExpansionEstimates` |
| Coefficient uniqueness, Lemma 5 | `CoefficientUniqueness`, `LogSquaredMesh`, `MF21CoefficientUniqueness` |
| Direct inverse-column and trace limit (26)–(29) | `FirstInverseColumn`, `FirstColumnAsymptotics`, `InverseTraceRecurrence`, `DiscretePowerLimits`, `TraceLimitSummation`, `TraceIntegralConstant`, `ToeplitzTraceLimit` |
| Even-zeta and irrational model trace (31)–(33) | `MF21TraceSeries`, `MF21Transcendence` and its six licensed source dependencies |
| Actual finite-head obstruction, Corollary 6 | `FiniteTraceObstruction`, `ActualTraceObstruction`, `FinalTarget` |
| Complete assembly | `FinalTarget`, `Solution` |

The finite inverse-column calculation replaces the original appeal to a
continuum Green-kernel limit. The revised equation (24) derives the finite-head
truncation bound directly from the uniform Taylor estimate and
`Y(jπh,h) = O(h)`, which is the route formalized here. The determinant proof
normalizes coalescing roots by `2 sin(theta/2)`; this has a simple zero at zero
and yields the same smooth quotients as the manuscript's local `theta`
normalization. These are proof changes, not changes to the mathematical target.

## Review and acceptance

`Challenge.lean` contains only independently reviewed specification
placeholders, importing the trusted definitions. `Solution.lean` proves the
same declarations in a separate environment and must never import Challenge.
`comparator.json` lists every advertised export, with no definition holes.

A local macOS raw-kernel build is a development check. Final acceptance also
requires the repository's fresh non-root Linux Comparator, its sandbox and
negative controls, exact source hashes, transitive axiom report, and
independent semantic reviews. Consult the retained verification receipts for
the actual completion status; this document is not a claim that those gates
have passed.
