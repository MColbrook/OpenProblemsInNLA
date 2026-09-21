# Historical development record

This is a dated, superseded snapshot from before TargetProof passed.
Its statements about unfinished work are historical; current status is in
[VERIFICATION.md](VERIFICATION.md). Original logs remain unchanged.

# Verification record: 20 September 2026

**MF-21 is not fully Lean-verified.** The main proposition
`MF21Restart.Target` has no proof. The restart establishes intermediate
results, with explicit remaining hypotheses where the manuscript uses its
earlier construction. This does not increase the completed-problem count.

## Actual local execution

The coordinator ran `python3 verify_local.py` in this project. The integrated
run recorded below started at `2026-09-20T23:21:57.714886+00:00` and returned
exit code 0 at `2026-09-20T23:35:53.699518+00:00`.
It compiled 112 modules sequentially, including the independent Challenge
and Solution modules, under `LEAN_NUM_THREADS=1`, `-j1`, and `-M4096`.

- [Immutable run record](evidence/runs/20260920T232157714886Z/record.json)
- [Axiom output](evidence/runs/20260920T232157714886Z/Audit.log)
- [Solution compilation log](evidence/runs/20260920T232157714886Z/Solution.log)
- [Challenge compilation log](evidence/runs/20260920T232157714886Z/Challenge.log)

The record SHA-256 is
`2cd1ffe95f742fb17a026600f769dbccde5e3854102b319de81d3ac81f8348f3`.
It records every Lean source hash, pinned configuration hash, dependency
commit, command, exit code, output hash and log hash. All source and
configuration hashes were checked for changes during the run.

The 348 component declarations printed by that run's Audit.lean use only
`propext`, `Classical.choice`, and `Quot.sound`. No proof-side `sorry`, custom
axiom, `unsafe`, or `native_decide` occurs in this restart. Challenge.lean
contains five deliberate statement placeholders used by the Comparator
protocol; Solution and all proof modules do not import Challenge.

LeanCert's actual successful call is in Numerics.lean. It proves the closed
bound `1 ≤ sqrt(2)` in kernel mode; the exact identity for `sin(pi/4)` and
linear arithmetic give the selected phase-window margin. There is no
parameter subdivision or numerical matrix enumeration.

The six external π-transcendence modules also compile in this run. Their
original authorship, immutable source reference, exact port changes and
independent source comparisons are retained in `vendor/gotrevor-pi/`.
The unconditional π theorem's axiom report is standard; it is not an added
transcendence assumption.

The concrete boundary criterion, eigenspace multiplicity bridge, full trace-series
arithmetic, stable-root construction, phase endpoints and monotonicity, and
exact normalized Laplace coefficient factorization, and complete real determinant
remainder of Lemma 3 are included in this run. The latter includes the actual
leading signs, normalization, subset partition, eigenvalue equivalence,
value/derivative estimates, and endpoint improvement. Their exact reviewed
hashes and successful logs are identified in the corresponding review
reports. The integrated record covers only the sources listed in it, not
later development modules.
Failed development logs are retained
under evidence/logs; their axiom output may include `sorryAx` from Lean's
error recovery and must not be represented as successful proof checks.

The following successful development runs are also retained separately;
their exact source versions are now included in the 83-module integrated run:

- `evidence/logs/spectral-window-bounds-01.json`: the actual high-phase
  remainder smallness used at the start of Lemma 4; one standard-axiom report.
- `evidence/logs/spectral-enclosure-03.json`: positivity of the actual Fourier
  matrix and its upper complement, and strict bounds on every in-range
  eigenvalue; three standard-axiom reports.
- `evidence/logs/weighted-binomial-inverse-02.json`: the finite telescoping
  identity toward the known inverse formula; three standard-axiom reports.
- `evidence/logs/actual-simple-roots-02.json`: a simple zero of the actual
  scalar residual gives a one-dimensional eigenspace and exactly one original
  one-based index; six standard-axiom reports. Identification of that index
  with its phase-cell label remains a separate obligation.
- `evidence/logs/phase-window-roots-02.json`: unique actual residual roots
  in every sufficiently high phase window; one standard-axiom report.
- `evidence/logs/final-phase-window-01.json`: eventual final-window geometry
  and exclusion of interior residual zeros; two standard-axiom reports.
- `evidence/logs/triangular-inverse-03.json` and
  `evidence/logs/fourier-binomial-stencil-02.json`: exact two-sided triangular
  inverses and the binomial formula for the actual Fourier coefficients;
  seven and two standard-axiom reports, respectively.
- `evidence/logs/matrix-inverse-algebra-02.json` and
  `evidence/logs/toeplitz-weighted-factorization-02.json`: the generic inverse
  algebra and actual weighted Toeplitz identity; four and one standard reports.
- `evidence/logs/toeplitz-inverse-01.json` and
  `evidence/logs/inverse-kernel-entries-01.json`: the actual inverse matrix,
  all finite entries, rising-factorial formula and reversal symmetry; four
  standard-axiom reports in each.

These logs do not establish root indexing, kernel convergence, or the full
Target. Their individual records give the exact source and output
hashes and actual commands. They also do not represent Comparator runs.
The root import and axiom audit include all the components listed above.
The integrated record covers them together with the earlier components;
it does not cover later development sources.

After that integrated run, these further local component tests passed:

- `phase-root-coverage-01`: every high actual residual zero belongs to an
  ordinary phase window with label at most n; one standard-axiom report.
- `spectral-order-01`: exact symbol endpoints/order, actual sorted-spectrum
  monotonicity, and unique interior angle for each in-range eigenvalue;
  five standard-axiom reports.
- `ordered-tail-counting-01`: finite ordered-array counting with explicit
  occurrence and coverage premises; one standard-axiom report. Applying
  this to the actual phase windows remains separate.
- `scaled-rising-02`: exact polynomial scaling and compact continuity,
  uniform continuity and bounds for the concrete kernel integrand;
  nine standard-axiom reports.
- `riemann-cell-bound-03`: the symbolic interval-sum error estimate from
  per-cell oscillation; one standard-axiom report.
- `scaled-inverse-sum-01`: the exact rescaled actual inverse is h times
  the concrete finite integrand sum, including its factorial factor and
  both t-x+h shifts; one standard-axiom report.
- `eta-neighborhood-02`: actual analytic eta and its first derivative are
  bounded on a slightly enlarged closed interval; one standard-axiom report.
- `phase-window-indexing-01`: all finite counting premises are discharged
  for the actual spectrum; each high phase-window label is its original
  one-based eigenvalue index, with a simple residual root; one standard report.

Each has its own JSON/log under evidence/logs. The current source, output,
and log hashes and exact standard-axiom report counts were checked against
those records. These eight modules were not included in the 83-module root
snapshot. Further actual component checks subsequently passed:

- `uniform-implicit-scalar-01`, `implicit-phase-01`: the uniform analytic
  implicit function is constructed by IVT, uniqueness and local IFT gluing.
- `parametric-taylor-02`, `implicit-taylor-01`: one exact derivative-defined
  coefficient family and an all-order uniform Taylor remainder.
- `vertical-power-factor-01`, `coefficient-vanishing-02`: actual power
  differentiation and every coefficient bound through order 2m, including x=0.
- `phase-quantitative-01`, `symbol-derivative-02`, `implicit-spectral-error-01`,
  `implicit-spectral-data-01`: quantitative actual eigenangles, identification
  with that same Y, and the exponential spectral error (25).
- `circulant-embedding-02`, `circulant-spectrum-01`: the actual principal
  block and full characteristic polynomial; sorted enumeration/interlacing remain.
- `kernel-riemann-approx-02`, `kernel-shifted-sum-01`,
  `inverse-kernel-grid-top-01`: uniform concrete integrand sums with the
  exact guarded inverse reindexing and one-cell endpoint shift.
- `inverse-kernel-continuity-02`, `inverse-kernel-grid-02`,
  `inverse-kernel-limit-01`: the literal reflected continuous kernel and
  uniform convergence of the actual inverse step kernel on the closed square.
  The reversal shift and clamped-ceiling index are proved explicitly.
- `actual-kernel-diagonal-01`, `grid-average-03`, `actual-trace-limit-02`:
  the actual kernel diagonal, continuous grid averages and the rational
  trace limit (29), with the exact n+2 normalization.

The 29 post-snapshot modules have source-matched evidence indexed in
`evidence/integration-06-inputs.json`. They contribute 74 new explicit axiom
reports, all standard-only. All 29 are now included in the successful 112-module integrated run above.
The exact record covers those sources and all 348 Audit declarations. The earlier attempt in
`evidence/runs/20260920T232033125167Z` was interrupted during preparation
and is explicitly not a successful integrated run.

Independent reviews include `reviews/uniform-implicit-phase-review.md`,
`reviews/implicit-taylor-review.md`, `reviews/coefficient-vanishing-review.md`,
`reviews/phase-quantitative-referee-b.md`, and
`reviews/inverse-kernel-limit-chain-referee-b.md`. The latter covers the nine
root-authored modules through the actual trace limit, with 31 standard-only
reports and explicit dependency-review exclusions. These are source reviews
of retained local runs, not independent compiler reruns or Comparator results.
The full Target remains unproved.

## Independent review

The reviewers did not run compilers; their work is independent source review,
with inspection of the coordinator's exact local evidence.

- [Manuscript audit](reviews/manuscript-audit.md): Sections 2–5; no false
  mathematical step found. This withdraws the earlier omitted-coefficient
  objection. It is informal mathematical review.
- [Legacy Lean audit](reviews/legacy-lean-audit.md): material statement and
  interface defects found; the old file cannot establish the canonical target.
- [Restart statement review](reviews/restart-statement-review.md): corrected
  quantifiers, one-based indexing, fixed bulk threshold and coefficient family.
- [Fixed-index and numerical review](reviews/fixed-index-numerics-review.md):
  proof fidelity and kernel-mode computational scope.
- [Bulk and definition-bridge review](reviews/bulk-and-bridges-review.md):
  the genuine scale gain, original Fourier integral, and positive index cutoff.
- [Independent contract and second proof review](reviews/contracts-and-fixed-index-review.md):
  fixed-index/numerical proofs and matching statement/proof interfaces.
- [Boundary and trace review](reviews/boundary-and-trace-review.md): exact
  determinant expansion and rational diagonal integral.
- [Recurrence basis](reviews/recurrence-basis-review.md) and
  [finite recurrence](reviews/boundary-finite-recurrence-review.md): actual
  solution space, ghosts and finite restriction/extension.
- [Fourier recurrence](reviews/fourier-recurrence-review.md),
  [Toeplitz action](reviews/toeplitz-recurrence-review.md), and
  [boundary/eigenvalue bridge](reviews/boundary-toeplitz-and-eigenvalue-review.md):
  integral-defined matrix, Laurent coefficients and determinant criterion.
- [Kernel and arithmetic](reviews/kernel-trace-pi-review.md),
  [external π proof port](reviews/pi-port-review.md), and
  [full trace series](reviews/trace-series-review.md): actual substitution,
  both parity formulas, positive rational correction and irrationality.
- [Quadratic root algebra](reviews/stable-root-algebra-review.md): actual
  square-root branch and root inside the unit disk.
- [Smooth roots and parameters](reviews/stable-root-smooth-and-parameters-review.md):
  principal-branch regularity, derivative, and exact root-of-unity substitution.
- [Individual phase](reviews/phase-factor-review.md): the positive-factor
  removal at zero and smooth principal arguments, preserving their sum.
- [Real/complex eigenvalue bridge](reviews/real-complex-eigenvalue-review.md):
  characteristic roots, complex eigenvectors and sorted real eigenvalues.

- [Root symmetry and endpoint components](reviews/root-and-endpoint-components-review.md),
  [phase at zero](reviews/phase-zero-review.md), and
  [phase monotonicity and analytic slopes](reviews/phase-monotonicity-analytic-slope-review.md).
- [Concrete root list](reviews/characteristic-roots-concrete-boundary-review.md),
  [boundary multiplicity](reviews/boundary-multiplicity-review.md),
  [determinant derivative](reviews/determinant-multiplicity-review.md),
  [simple determinant zeros](reviews/simple-determinant-review.md), and
  [spectral multiplicities](reviews/eigenvalue-multiplicity-review.md).
- [Root tangents and differences](reviews/root-tangents-differences-review.md) and
  [normalized coefficients](reviews/vandermonde-normalized-boundary-review.md):
  actual endpoint derivatives, exact vanishing powers, and nonzero leading coefficients.
- [Product decay](reviews/boundary-product-decay-review.md),
  [smooth error coefficients](reviews/normalized-quotient-error-coefficient-review.md),
  [phase product](reviews/phase-product-review.md), and
  [finite remainder bounds](reviews/boundary-error-bounds-review.md).
- [Boundary conjugation and normalizer](reviews/boundary-conjugation-normalizer-review.md),
  [leading coefficients](reviews/leading-boundary-coefficients-review.md), and
  [normalization and complete remainder, referee A](reviews/leading-normalization-determinant-remainder-referee-a.md), and
  [referee B](reviews/leading-normalization-determinant-remainder-referee-b.md).

The pinned review rubric is [REFEREE_STANDARDS.md](reviews/REFEREE_STANDARDS.md).

## Checks not run

The real leanprover Comparator, independent kernel replay, and Linux sandbox
checks have **not** run for this restart; there is no GitHub run ID. The
five-component comparator.json is prepared and its two modules compile
locally, which is not a Comparator result. It does not configure the full
MF-21 target. No new upstream PR or solved-status change has been made.

The metadata passed the official formalization.yaml v0.4 JSON schema using
Ruby YAML.safe_load followed by jsonschema.Draft7Validator. The metadata and
schema hashes are recorded in [metadata-validation.json](evidence/metadata-validation.json).
Metadata validation checks record structure, not mathematical correctness.

## Remaining mathematical formalization

The unchanged manuscript still requires quantitative eigenangle/phase
comparison and circulant interlacing; uniform implicit
Taylor construction and endpoint jets; combination into the lower-order and
bulk estimates; and the inverse-kernel and trace-limit contradiction.
The diagonal substitution, its rational integral, and the exact series
irrationality are proved as separate components; the inverse-kernel limit
and identification with the limiting matrix trace are not. Missing formal
proofs of these facts are not evidence of a
mathematical gap. No contradictory pair of trace limits is assumed outright.
