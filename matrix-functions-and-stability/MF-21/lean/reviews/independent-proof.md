# Independent proof, semantic-bridge and reuse review

**Phase:** post-implementation review. **Reviewer:**
`/root/independent_proof_referee`, an independent, nonimplementing Codex AI
agent. **Date:** 2026-09-20. **Verdict:** approve the reviewed source; no
material mathematical, fidelity, or attribution correction requested.

This approval is specific to the source bytes at local revision
`e378ec4679f9119aacf79a0fe30b80493a61ec5b`, recorded in
[independent-proof-hashes.json](independent-proof-hashes.json). I wrote no
proof code and made no proof edits. This report is independent of the
implementers' assessments. It does not substitute for the separate build,
transitive axiom, and sandboxed Linux Comparator gates.

## Scope and independence

I read the repository review protocol, the canonical problem README, the
complete parent `solution.md`, `NUMERICAL_TARGETS.md`, the Challenge,
definitions, Solution exports, and final witness assembly. I close-read 66
Lean files (9,027 lines), listed explicitly in the accompanying inventory.
The main independent scope is the stable-root and phase construction;
normalized determinant, leading terms and finite remainder; actual spectral
indexing; circulant and trace inputs; trace arithmetic and obstruction; and
all six imported pi-transcendence source files. I also inspected the common
coefficient construction and final target/uniqueness bridges.

This is not a claim to have close-read every local proof or all of Mathlib.
The separate fresh, nonimplementing fidelity referee's report covers 39
files, including the generic uniform inverse/Taylor machinery,
inverse-column asymptotics, boundary-kernel correspondence, simplicity,
Fourier correspondence, and coefficient uniqueness. The union of that
explicit scope and mine covers all 83 local Lean files, including the
placeholder Challenge. I independently checked that its source inventory
still matches every current source hash. The supplementary implementer
cross-review is useful corroboration but is not counted as an additional
independent referee verdict.

## Target and witness fidelity

`MF21Challenge.toeplitz` is the actual real symmetric, nonperiodic
signed-binomial matrix. The public Fourier equality has the original
normalization, integration limits, and exponent sign; it is an exported
theorem, not an assumption hidden in the matrix definition. The eigenvalues
are Mathlib's actual Hermitian eigenvalues with multiplicity, reversed from
its decreasing enumeration. I checked that convention against the pinned
Mathlib source. A Lean index `j : Fin n` corresponds to source index `j+1`.
The grid is exactly `(j+1)*pi/(n+2)` and the lower bulk index is the ceiling
of the square of the natural logarithm of `n+2`.

The final result ranges over every natural `m >= 3`. Its single coefficient
family is independent of dimension and eigenvalue index; it is continuous
on the closed interval, and its leading coefficient is the symbol there.
Each uniform bound has constants independent of `n,j`. Every lower order
through `2m-1`, the top bulk order, and the failure of top uniform order use
the same `model.d` witness. This is visible in `FinalTarget.targetAt`, rather
than inferred from names of custom predicates.

The stronger universal obstruction quantifies over **every** continuous
family, without assuming its leading coefficient or any lower-order
expansion. The proof restricts a hypothetical uniform top estimate to the
bulk, uses closed-interval coefficient uniqueness, and contradicts the
constructed family's obstruction. `smooth_common_family` additionally
retains that identical witness for smoothness, an all-index upper bound at
scale `(n+2)^(-2m)`, and a strictly positive lower bound at that scale in a
fixed finite head for every sufficiently large dimension. The offending
index may depend on dimension; the theorem does not claim a single index
works eventually. The exact exported statement matches this distinction.

## Root, determinant and indexing proof

The stable root is selected from the reciprocal quadratic only after its
domain conditions are established. The proof excludes unit-circle roots
for each nontrivial root of unity, proves uniqueness inside the disk, and
matches that root to the endpoint continuation. The endpoint substitution
`r = 1 + t*U`, with `t = 2*sin(theta/2)`, has limiting equation
`U^2 + omega = 0` and a nonzero derivative at the chosen branch. The analytic
implicit-function argument supplies a fixed smooth neighborhood, avoiding
an unjustified inference from pointwise infinite differentiability. The
resulting phase has the required endpoint values, including
`eta(0)=(m-1)*pi/2` and `eta(pi)=pi`.

`BoundaryNormalization` performs explicit binomial row transformations of
determinant one and extracts the precise power of the endpoint parameter.
The determinant expansion is a finite permutation sum. Its two leading
selections are disjoint, their relative sign is proved by swapping the unit
columns, and the remaining selections have a decaying root factor after
the normalization cancellations. The smooth coefficient and nonzero-base
conditions needed by the finite exponential-sum derivative estimate are
proved on the compact closed interval. Consequently its constants do not
silently depend on matrix dimension.

I checked the possible collision at `theta=pi`: nonvanishing is required
within each separate Vandermonde block, not between the two blocks. The
unit columns may coincide there without invalidating those normalizers.
The sine phase and normalizer are related by explicit algebra, rather than
by an assumed sign of a complex determinant. Conjugation permutations
give the reality needed for the real error equation. The coincident unit
columns also prove exact endpoint vanishing of the real error. Together
with its derivative bound, that identity excludes the artificial final
phase cell; merely having a small error would not suffice.

The phase-cell analysis proves existence, uniqueness and nonzero derivative
of the relevant roots and excludes roots in the gaps. `ActualPhaseIndexing`
instantiates these estimates with the actual determinant. The top-down
counting argument uses the determinant/spectral multiplicity bridge to
identify the actual increasing eigenvalue index. It does not assume the
low-index asymptotic being proved or global simplicity. The subsequent
angle estimate therefore concerns the original spectrum, not an
independently constructed model spectrum.

## Trace obstruction and arithmetic

The Toeplitz Gram factorization is a concrete finite-difference matrix
identity. Its first square block is triangular with diagonal one, proving
injectivity and positive definiteness. The circulant embedding has an
explicit no-wraparound argument; its ordered Fourier samples, the
compression inequality and the strict upper spectral endpoint supply the
actual reciprocal-eigenvalue majorant. Positivity and dimension conditions
are discharged at the uses of inverses and reciprocal estimates.

The inverse-trace recurrence follows from an explicitly verified rank-one
correction and telescoping. With the independently reviewed inverse-column
asymptotics, `TraceLimitSummation` and `TraceIntegralConstant` produce the
actual normalized inverse-trace limit, including the `n+2` normalization.
The beta integral is evaluated to a rational factorial expression. The
comparison trace is the actual summable shifted reciprocal-power series,
not a supplied asymptotic premise.

`MF21TraceSeries` splits odd and even `m`, applies Mathlib's even-zeta
evaluation, and subtracts the finite initial tail. For every `m>=3` that
correction is positive. The resulting rational term minus a nonzero
rational multiple of `pi^(-2m)` is irrational, so it differs from the direct
rational trace limit. I checked the generic `TraceArithmetic` helper as
well as this unconditional instantiation; the former's conditional
interface is not a remaining hypothesis in the exported theorem.

`FiniteTraceObstruction` uses separation of these two limits and a uniform
summable tail bound to force a discrepancy in a fixed finite head for
every sufficiently large dimension. It does not assume convergence of
each rescaled low eigenvalue. `ActualTraceObstruction` supplies its
positivity, tail, trace, and model-profile premises for the real matrix and
the same Taylor family. Its transfer to the original remainder scale gives
the strict positive lower bound and hence rules out a uniform extra factor
of `(n+2)^(-1)`.

## Imported proofs, reuse and provenance

I read all six vendor files, including the full Lindemann and
symmetric-polynomial argument, not just the final pi wrapper. Their chain
proves `Transcendental Q Real.pi`: the analytic approximation, integral
nonvanishing argument, clearing of polynomial denominators, conjugate
subset-sum construction, and Euler identity are connected by actual
theorems. `HermiteLindemann` transports algebraicity between fields; it
does not postulate the desired transcendence. The imported Mathlib
analytic-approximation statement and its proof were selectively checked
against the pinned source.

I independently recomputed every canonical vendor hash and reversed the
documented import renames and the one explicit `powersetCard_zero_right`
simplification addition. All six recovered hashes agree with the declared
upstream snapshot. I did not make a fresh network fetch; the separate
cross-review records that check. The Apache-2.0 license, authorship,
original proof provenance and AI-assistance disclosures are preserved.

I searched the pinned Mathlib matrix, recurrence, Vandermonde,
symmetric-polynomial and number-theory sources and inspected the relevant
eigenvalue, zeta, Lindemann, Vieta, Newton-identity and symmetric-polynomial
APIs. The local proofs reuse these APIs. The bounded search found no
direct replacement for the specialized finite compression/indexing or
Toeplitz determinant arguments; this is not a claim that every possible
Mathlib alternative was excluded. Namespaces and the split between generic
lemmas and actual MF-21 instantiations make the dependencies reviewable.
Broad imports retained in the vendor bundle are not a mathematical or
provenance defect.

The earlier recorded limitations concerning matrix identification,
endpoint smoothness, determinant/indexing inputs, and conditional trace
arithmetic are closed by the concrete paths described above. Historical
component approvals are not treated as approvals of the final theorem.

## Mechanical evidence and limits

I inspected the retained canonical macOS replay receipt, Challenge receipt,
Solution axiom log, and generated transitive axiom-audit source/output.
I independently compared all 82 compiled module hashes with the current
files and all module-log hashes with the receipt. Every recorded module
exit is zero. All 1,354 parsed axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`; the five Solution exports have those
same permitted dependencies. The Challenge elaboration records its five
intentional placeholders. A separate comment/string-aware scan of all 83
local sources found those five placeholders and no forbidden proof token
in the implementation.

These are inspections of retained evidence, not a build run by this
reviewer. In particular, the macOS replay explicitly trusts external
dependency caches whose revisions were unavailable to that runner. It is
development evidence and cannot establish the independent pinned Linux
Comparator gate.

I subsequently inspected the fresh retained
[Linux evidence](../verification/linux-2026-09-20/result.json), produced by
the separate runtime agent. The receipt reports Lean 4.33.1 on aarch64 Linux
and the source-lock hash matches this repository. Dependency acquisition
records the pinned Mathlib and other package revisions. I independently
matched all 96 input hashes against both the current files and every member
of the trusted-input archive, and checked the exact five-theorem Comparator
configuration. The full-log archive agrees with the individual retained
run logs. Result, Comparator-log and archive hashes agree with the evidence
summary.

The actual Comparator log records successful Challenge and Solution builds,
export of all five selected contracts, default-kernel acceptance, final
`Your solution is okay!`, and exit status zero. I parsed all 251 complete
printed axiom reports from that full log, including multiline lists; each
uses only the permitted three axioms. The convenience `actual-axioms.log`
excerpt is line-filtered, so it was not used as the sole source for complete
axiom sets. The sandbox controls record filesystem, network and namespace
restrictions; the kernel controls reject an invalid raw proof and quotient
mismatch; Comparator controls reject a theorem-statement mismatch and
illegal axioms; and separate `sorryAx` and native-decision fixtures are
rejected. Their expected failure statuses are distinct from the successful
MF-21 run.

This supports the actual Linux acceptance gate for these exact reviewed
contracts and source bytes. It is an independent inspection of the retained
run, not a rerun by this reviewer or a full audit of the verifier's own
implementation. The inventory records the evidence hashes and these
limitations. Semantic approval remains the source judgment above, not an
inference from kernel acceptance.
