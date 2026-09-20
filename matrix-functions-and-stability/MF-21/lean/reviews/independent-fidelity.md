# MF-21 independent final fidelity and scope review

Date: 20 September 2026 (UTC). Reviewer: `/root/final_fidelity_referee`, an
independent, nonimplementing OpenAI Codex AI agent. This is an AI-agent review,
not external human peer review. I wrote no mathematical proof or specification
code for this package.

**Verdict: approve the frozen mathematical statement and its source-to-formal
correspondence.** I found no material mismatch, vacuous final hypothesis, or
substitution of an auxiliary result for the complete MF-21 target. This verdict
is a semantic review, not a declaration that every repository acceptance gate
has passed. Mechanical verification and the additional independent-review
requirements remain separate.

## Reviewed snapshot and scope

The reviewed project is the canonical `matrix-functions-and-stability/MF-21/lean/`
package, not the earlier flat development project. Its base revision was
`bd3f7a055e1376c573ef9036124a86833641f9f1`; the new package was uncommitted when
read. Exact SHA-256 values are retained in
[independent-fidelity-hashes.json](independent-fidelity-hashes.json), whose
SHA-256 is `5ad4b2ebd2ae61f6283e824f67da2e4272e5d8e6cbe3c329cdf9b6207c892771`.

| Frozen boundary file | SHA-256 |
| --- | --- |
| `Challenge.lean` | `7e7f7d89e0e26cd21c5cf6b3d9c3ca78f1b7bf6580cfe4f12a0666e84c267fd1` |
| `MF21/Definitions.lean` | `bf813d493c38164aa8f4b3a6fc4476c2b57560b0bd87932b02ab1a4d94038525` |
| `Solution.lean` | `8f21de690dff7251125fb3ec5601e8578db2203c941e6c8675290108b29a4aa6` |
| `comparator.json` | `d1336933e08ecb99189d6b1caf73e7e2be4818a3a5a0d97861d89e508a44856a` |
| `NUMERICAL_TARGETS.md` | `3e49b609e5d165202cb2a4c485c402fed9360f84e04408b1f325063e69984bb1` |

I read the canonical problem README, the entire revised `solution.md`, the
numerical-target document, the independent specification, definitions, final
exports, and the repository review protocol. I independently checked the
primary [Barrera–Böttcher–Grudsky–Maximenko preprint](https://arxiv.org/pdf/1710.05243),
particularly Theorem 1.2, Remark 8.3, and Conjecture 8.4 on printed page 26.
The manuscript's added smoothness, universal obstruction, and finite-head
sharpness were reviewed as additional claims rather than silently substituted
for the original conjecture.

The hash inventory lists 39 modules that I read closely, including all
definitions and the complete assembly, coefficient uniqueness, mesh density,
implicit inverse, Taylor estimates, expansion transfer, Fourier identification,
inverse-column calculation, spectral boundary bridge, trace obstruction,
and their actual-object connections. I also scanned the canonical local
source inventory for admissions, custom axioms, unsafe proof mechanisms,
definition replacement and imports of `Challenge`. The inventory records all
local Lean source hashes; it does not claim that I independently rederived
every tactic proof in all 82 implementation modules. In particular, the full
vendored Lindemann argument and the lower-level characteristic-root algebra
require their own proof review and mechanical checks.

## Exact target and nonvacuity

`FullTarget` quantifies over every natural `m` with `3 ≤ m`, then chooses one
real coefficient family. The family is outside the dimension and eigenvalue
index quantifiers. Its entries through `2m` are continuous on the entire
closed interval, and `d 0` equals the actual symbol there. Every lower order
`p ≤ 2*m - 1` has constants independent of `n,j`. The bulk estimate has the
exact exponent `2m+1`, and the same-family obstruction negates precisely that
all-index estimate. Nothing restricts `m` to finitely many examples.

`j : Fin n` represents source index `j.val+1`. The sample point is exactly
`(j.val+1)*pi/(n+2)`, and the truncation includes indices `0,...,p`.
`Nat.ceil ((Real.log (n+2))^2)` gives the source's squared natural logarithm
cutoff for integer indices. The asymptotic quantifiers include all sufficiently
large dimensions; dimension zero cannot make them vacuous. Values of the
coefficient functions outside the closed interval are irrelevant to the target.

`LogSquaredMesh` proves both that the cutoff is eventually below the dimension
and that clipped admissible sample indices converge to every point of
`[0,pi]`, including both endpoints. Thus the uniqueness proof does not rely
on an empty bulk range or an assumed density theorem. The generic uniqueness
induction uses only the single highest-order difference estimate, together
with within-interval continuity; it does not assume lower-order remainder
estimates for a hypothetical family.

The separately exported `UniversalObstruction` correctly omits a prescribed
leading coefficient: `universalObstruction_of_fullTarget` first obtains the
constructed bulk family and then uses actual closed-interval uniqueness to
identify any hypothetical continuous all-index family with it.

## Actual matrix and spectral bridge

The trusted matrix is the real signed-binomial Toeplitz matrix at the natural
distance of the row and column indices. `Nat.choose` sets coefficients beyond
the bandwidth to zero; no periodic wraparound is present. The selected
`fourier_matrix_entries` theorem proves entrywise equality to the exact source
integral, including the factor `1/(2*pi)`, interval `[-pi,pi]`, and negative
Fourier exponent. `FourierCoefficients` handles both integer signs and
out-of-band coefficients explicitly. This discharges the bridge that the
earlier statement reviews had left open.

I inspected the pinned Mathlib `Analysis/Matrix/Spectrum.lean` definitions of
`eigenvalues₀`, `eigenvalues₀_antitone`, and
`roots_charpoly_eq_eigenvalues₀`. The package uses the actual Hermitian
eigenvalues and reverses their order with `Fin.rev`, preserving multiplicity.
The later `eigenvalue_monotone` and characteristic-polynomial bridge agree
with this convention. These are not freely chosen numbers satisfying an
assumed expansion.

`BoundaryDeterminant` identifies the finite matrix equation with the centered
recurrence and zero ghost values. Restriction of the boundary kernel is
proved injective, and the explicit linear equivalence to the true complex
eigenspace supplies its exact dimension. `ActualBoundaryDeterminant`
discharges distinct-root and characteristic-polynomial hypotheses before
connecting determinant zeros to the actual sorted real eigenvalues.

The phase-root indexing path uses the real normalized determinant identity,
a nonzero normalizer, endpoint cancellation at `pi`, and the actual error
bounds. Its simple-zero argument passes through determinant differentiation,
kernel dimension one and a diagonalizing basis; it does not equate geometric
and algebraic multiplicity without justification. The top-down matching
argument only uses simplicity in the controlled tail and explicitly excludes
the artificial endpoint root. `ActualTailAngles` supplies the tail hypothesis
needed by the expansion assembly rather than leaving it assumed.

## Common smooth family and all expansion orders

`Model` contains genuine requirements, not a renamed conclusion. Crucially,
`model_exists` proves that this structure is inhabited from the root-defined
phase and a uniform implicit inverse. `actualModel` depends on `m`, not on
`n`, `j` or the expansion order. `Model.d` is the vertical derivative of
`g(Y)` at step zero, divided by the factorial, matching equation (5).

The inverse is constructed on an enlarged interval; its ambient smoothness
at the boundary of the compact strip is proved by agreement with the local
implicit-function branch. The Taylor proof bounds derivatives on a common
compact strip and retains one coefficient family at every order.
`Model.d_smooth` proves ambient smoothness at every point of the closed
coefficient interval, which is sufficient for the exported `ContDiffOn` claim.
`Model.d_zero` proves the leading-symbol identity.

`SymbolTransfer` uses the actual symbol's order of vanishing to gain the
factor `h^(2m)` from an exponentially small angle error. The finite-head
bound combines circulant interlacing with the implicit model's `O(h)` angle
bound. `ExpansionEstimates` then proves every lower order and the top bulk
order. `ExponentialCutoff` obtains the extra factor `1/(n+2)` from the exact
logarithm-squared cutoff. The revised equation (24) follows the finite-head
Taylor route; no separate unproved claim about individual coefficient
vanishing is used.

## Trace obstruction and sharpness

The finite-column proof fixes `m=r+1`, uses a polynomial of degree below
`2m`, checks all omitted ghost values and the single nonzero left ghost,
and proves the exact equation `A*u=e_0`. Invertibility identifies this
candidate with the actual inverse column. Its polynomial rescaling and
Riemann-sum limit feed the exact inverse-trace increment formula. The final
trace theorem concerns the reciprocal sum of the actual target eigenvalues,
with normalization `(n+2)^(-2m)`.

`modelTrace` is the genuine convergent shifted reciprocal-power series.
The odd and even cases subtract nonzero rational finite corrections from the
appropriate even-zeta value. The transcendence input is a proved statement
about `Real.pi`, not a hypothesis of a selected theorem. The arithmetic
inequality is instantiated against the exact rational inverse-trace limit.

`FiniteTraceObstruction` separates a fixed finite head from both uniformly
small tails. Its reciprocal continuity step is legitimate because the model
profile is positive; it does not assume the disputed fixed-index eigenvalue
limit. `ActualTraceObstruction` supplies the actual positivity, summable
reciprocal majorant and trace limit, then transfers the discrepancy to the
Taylor approximant's independently proved profile. Consequently the lower
bound holds in every sufficiently large dimension at some index in one
fixed finite set. The index may vary with dimension, exactly as the revised
corollary says. `model_not_uniform` uses this lower bound, not equation (25)'s
upper bound, to contradict any proposed order `2m+1` uniform remainder.

The selected `smooth_common_family` combines this finite-head lower bound
and the matching all-index upper bound with the same family used by every
expansion estimate. There is no switch of existential witnesses.

## Earlier findings and evidence actually inspected

I read the two 19 September statement reports. Their matrix/Fourier bridge,
stronger smoothness and unproved analytic-input limitations are resolved in
the final source paths described above. Their original mathematical target
has been preserved. Those historical reports are not final proof reviews by
nonimplementers; their authors later contributed implementation. This review
is itself post-implementation, and does not claim that the new stronger
export statements were reviewed by me before implementation.

I inspected the fresh canonical development replay receipt, the five final
export axiom lines, the complete generated axiom-audit output by parsing its
entries, and the separate challenge compilation log. The receipt is retained
at `reviews/2026-09-19-mf21/verification/canonical-source-replay/result.json`
and has SHA-256
`2e39b4ef36de938e44618416e164f674636076907fe2f9974e660530bf5414eb`.
It records 82 successful `--trust=0` module compilations, no unfinished
modules and no changed source hashes. The generated audit contains 1,354
declaration entries, all using only subsets of `propext`, `Classical.choice`
and `Quot.sound`. The five final exports each print that permitted set.
The trusted challenge separately emits exactly five expected placeholder
warnings; the solution import graph excludes it.

These are macOS development receipts produced by another agent, which I
inspected rather than generated. The receipt explicitly trusts external
compiled dependency caches whose revisions were unavailable for rechecking;
it is not the authoritative fresh Linux Comparator result. I have not yet
inspected an MF-21 Linux Comparator receipt or its problem-specific negative
controls and do not certify them here. No target should be promoted on the
strength of this review alone. Any later change to the mathematical boundary
or proof sources requires checking against the retained hashes and reopening
the affected review scope.
