# MF-21 scoped independent cross-review

**Phase:** post-proof source review. **Reviewer:** `/root/lean_audit`, an AI
agent. **Date:** 2026-09-20. **Reviewed revision:**
`e378ec4679f9119aacf79a0fe30b80493a61ec5b`.

**Verdict: approve within the independent scope listed below.** I found no
material mathematical or specification defect in that scope. This is an
additional cross-review by a contributor, not a claim to be an independent
referee of the entire package. The two separate final referees and the
mechanical acceptance gates retain their own responsibilities.

The companion [hash record](independent-cross-review-hashes.json) identifies
the exact bytes of all 48 fully read source files (6,832 lines), the context
documents, and the ownership exclusions. It is the authoritative scope of
this report. I read complete proof bodies in the listed files, not just
declaration signatures or authors' PASS messages. I also read
`NUMERICAL_TARGETS.md` and the repository's independent review protocol.

## Independence and exclusions

I implemented substantial parts of this formalization. In particular, I do
**not** count as independently reviewed here my definitions, coefficient
uniqueness and mesh modules, first inverse column and its asymptotics,
boundary determinant/spectrum/kernel modules, smooth quantization and Taylor
modules, model/expansion transfer modules, or `FinalTarget`. I conservatively
exclude the historical conditional `TraceArithmetic` helper as well. The
complete excluded-file list is in the hash record. Reading these as context
does not turn this into an independent review of their proofs.

The fresh nonimplementing fidelity referee was explicitly given that list
and reported independently reading those modules. A second fresh
nonimplementing proof referee was subsequently assigned; I sent that referee
my scope and findings. Those reports, not this one, determine their own
coverage and verdicts. I changed no proof source during this review and made
no GitHub writes.

## Stable roots, endpoint regularity, and phase

I independently read `BulkRoots`, `BulkImplicit`, `BulkEndpoint`,
`BulkRootFamily`, `BulkPhase`, `BulkTotalPhase`, `BulkEta`, `BulkSymbol`,
`BulkSlopes`, `BulkDecay`, and `BulkLeadingPhase`.

The stable root is selected from the actual quadratic equation. Existence,
nonvanishing, strict modulus less than one, and uniqueness are proved on the
specified domain; the default value of the total definition is not used to
assert those properties off that domain. Root-family distinctness uses the
distinct roots of unity and the separation of stable, unit, and reciprocal
moduli. The two unit roots are distinct on the open interval, as required by
the boundary criterion.

The endpoint desingularization uses an analytic implicit-function theorem
for the rescaled quadratic. This matters: it supplies one neighborhood with
all smooth orders, rather than incorrectly deriving such a neighborhood
from pointwise `ContDiffAt` of order infinity. Its derivative selects the
decaying branch for positive arguments. The phase factors have positive real
part, so the principal argument introduces no branch jump. The finite sum
gives exactly `psi(0) = (m-1)*pi/4` and `psi(pi) = 0`; the extension has
`eta(theta) = theta + 2*psi(theta)`, with `eta(0) = (m-1)*pi/2` and
`eta(pi) = pi`.

The slope normalizer is a product of the two separate block Vandermonde
determinants. Each block is proved nonsingular on the closed interval. At
`pi` the two unit roots coincide across the blocks, which does not contradict
this normalizer's nonvanishing. The full boundary determinant's endpoint zero
is treated separately. Compactness of the smooth slopes, nonzero extended
roots, and logarithmic derivatives supplies finite constants; no uniform
bound is merely asserted from an interior-only estimate.

## Exact determinant normalization and error bounds

I independently read `BoundaryNormalization`, `BoundaryBlockForm`,
`BoundaryLeadingTerms`, `BoundaryExpansion`, `BoundaryDecay`,
`ActualBoundaryDecay`, `ActualBoundaryError`, `ActualBoundaryExpansion`,
`ExponentialSums`, `BoundaryReality`, `PhaseRotatedError`, `RealBoundaryError`,
`ActualBoundaryPhase`, and `ActualBoundarySmooth`.

The binomial row operations have determinant one and extract exactly the
factor `(2*sin(theta/2))^(m*(m-1))`. The finite permutation expansion, its two
disjoint dominant selections, and the remaining terms are exact identities.
The combinatorial loss lemma shows that every remaining selection either
includes a stable nonunit root or omits its reciprocal partner. Consequently
every normalized remainder base has a common strict exponential decay.
The derivative calculation includes both coefficient derivatives and the
large-power logarithmic derivative; the claimed linear factor in the matrix
dimension is accounted for.

The signs in the two leading terms and the phase rotation agree. The result
is the actual phase `(n+2)*theta-eta(theta) = (n+1)*theta-2*psi(theta)`.
Conjugation of the full determinant is a permutation of sign minus one, and
the nonzero sine normalizer has the corresponding conjugation property.
These establish that the normalized complex remainder is real; taking its
real part does not discard an unproved imaginary constraint. At `pi` the
duplicated unit-root columns give a zero determinant, hence zero real error.
The derivative bound then gives the additional `pi-theta` factor needed to
exclude the artificial final endpoint cell.

## Actual spectrum, multiplicity, and index assignment

I independently read `SpectralTrace`, `SpectralSimplicity`, `Eigenangles`,
`ActualBoundarySimplicity`, `PerturbedPhase`, `PhaseCellRoot`,
`TopDownIndexing`, `PhaseIndexing`, `PhaseCutoffs`, `PhaseErrorEstimate`,
`ActualPhaseIndexing`, and `ActualTailAngles`.

These modules use the actual ordered Hermitian eigenvalues. The symbol is
strictly increasing on `[0,pi]`; the proved strict spectral endpoint bounds
give unique interior eigenangles. The spectral trace formula reindexes
Mathlib's eigenvalues correctly, including the reversal in the target.
The simplicity bridge uses a diagonalizing basis and a one-dimensional
complex eigenspace to rule out two eigenvalue indices at the same simple
secular zero. Its kernel-dimension input comes from an explicitly imported
module that I authored and therefore exclude from this independent scope.

Root localization proves one simple zero in every full tail phase cell.
The top-down matching argument additionally proves that every eigenangle
above a chosen cell is covered by the constructed tail roots. It uses
multiplicity and the exclusion of the final artificial endpoint cell; it
does not assume the desired index assignment or a count of the unknown low
roots. The cutoff constants are chosen independently of `n` and the index.
The final actual-angle theorem discharges the generic error and spectral
premises before passing an unconditional tail-angle approximation to the
expansion modules.

## Trace contradiction and the positive lower bound

I independently read `ToeplitzTraceLimit`, `MF21TraceSeries`,
`FiniteTraceObstruction`, and `ActualTraceObstruction`.

The trace limit assembly uses exact inverse-trace increments and converts
the first-column norm limit into the rational constant by a proved
telescoping limit and beta-integral evaluation. The independently scoped
assembly has no assumed Toeplitz trace limit. I do not claim here to
independently review the first-column modules I wrote or the full bodies of
every other imported trace helper.

The model trace is the actual shifted reciprocal-power series, with shift
`j+1+(m-1)/2` in zero-based indexing. The odd and even cases reduce respectively
to integer and half-integer zeta tails. For `m >= 3` the removed rational
correction is positive. The unconditional transcendence theorem makes the
model trace irrational, whereas the actual trace limit is rational.

The abstract finite-head lemma handles the first reciprocal coordinate
without requiring a majorant there; a summable uniform tail bound suffices.
The exact spectral majorant and actual trace limit discharge its premises.
The conclusion is eventual separation on one fixed finite set, not just the
existence of a divergent subsequence. Continuity of inversion transfers the
separation back to scaled eigenvalues. Uniformity over that finite set then
transfers it to the same model coefficient family, yielding a strictly
positive lower bound on the original `h^(2*m)` scale. This is precisely the
missing logical ingredient in the criticized upper-bound argument.

## Pi-transcendence provenance, closure, and reuse

I fully read the six vendored proof files and the `MF21Transcendence` wrapper.
The final statement is `Transcendental ℚ Real.pi` without an arithmetic
hypothesis. The intermediate conditional helpers are discharged by the
analytic approximation theorem, the integer nonvanishing argument, root-sum
integrality, and the symmetric-polynomial construction. The identifier
`transcendental_pi_axiomClean` names a theorem with a proof, not an axiom.
Historical comments about previously open ingredients are contextualized by
the final capstone and do not represent residual formal premises.

I independently fetched all six source files from the declared upstream
commit `3a24a73416f83c32b4d4a2ac09588524c6291650` using HTTPS and system curl.
Every fetched SHA-256 matches `provenance.json`. Every canonical file matches
its adapted hash. Reversing only the declared import-prefix changes and the
single `Multiset.powersetCard_zero_right` simplification change reproduces
every upstream byte hash. Thus the compatibility change did not alter a
statement or introduce an undocumented mathematical edit. The Apache-2.0
license and upstream AI-assistance/proof provenance disclosures are retained.

I searched the pinned Mathlib source's number-theory and analysis trees for
an existing real-pi transcendence theorem. That search found no such theorem;
the pinned Lindemann directory contains `AnalyticalPart.lean`. Reusing that
analytic theorem and the attributed external algebraic completion is
appropriate. The MF-21 modules also reuse existing spectral, implicit
function, Vandermonde, symmetric-polynomial, compactness, and zeta APIs.
Some small scalar helper results overlap across development modules, but
this is not a correctness or scope defect.

## Mechanical evidence and limits of this review

A comment/string-aware scan of the 48 reviewed source files found no `sorry`,
`admit`, `axiom`, `native_decide`, or `unsafe` token. This is only a source
check, not a substitute for transitive axiom inspection. The hash record
contains the scan result and exact file hashes.

I did not run a new full kernel replay or the Linux Comparator in this
cross-review, and I have not treated another agent's progress message as a
completed acceptance receipt. Fresh builds, transitive axiom checks,
Challenge/Solution equivalence, isolation, and negative controls are separate
mechanical gates. This report grants no independent approval of my own code
and does not by itself establish that the complete formalization is accepted.
