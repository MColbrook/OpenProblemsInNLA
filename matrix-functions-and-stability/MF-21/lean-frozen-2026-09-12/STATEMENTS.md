# MF-21 restart: statement lock and obligations

The unchanged manuscript is frozen at commit
`eb37bc17a462177f57efa270e9a9f9b17e9d88e2`, SHA-256
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`.

`MF21Restart.Target` states all three parts simultaneously for every integer
`m ≥ 3`, with one common family of coefficients and the actual ordered
Toeplitz eigenvalues. Published `j = 1,...,n` maps to `Fin n` index `j-1`.
`TargetProof.lean` now proves this proposition, and the stronger smooth
coefficient theorem, for exactly the same family. Actual execution evidence
is recorded in VERIFICATION.md.

The cosine coefficient is connected to the original complex Fourier integral
by the proved even-symbol symmetry argument.
Adding `1 ≤ j` to the bulk predicate changes no admissible index because
`ceil(log(n+2)^2) ≥ 1`. Both bridges are proved in StatementBridges.lean.

The proof obligations follow the manuscript, without assuming the conclusion:

1. Smooth stable-root branches and phase, including endpoint values: (2)–(8).
2. Normalized, grouped Laplace expansion with bounds on coefficient ratios:
   (13)–(18). Raw determinant terms include expanding roots and are not all
   contractive.
3. Determinant/eigenvalue equivalence, root counting from the upper endpoint,
   and the eigenangle bound: Lemma 4, (19)–(20).
4. Circulant embedding and interlacing: (21)–(22).
5. Taylor coefficients of `g(Y(x,h))`, uniform Taylor remainder (23), and
   coefficient vanishing estimates (24).
6. For `j ≥ J`, the approximation error is
   `C h^(2m) j^(2m-1) exp(-c j)` as in (25). The Taylor remainder is
   `O(h^(p+1))`, without an exponential factor. The extra power of `h`
   comes only after imposing the logarithmic bulk threshold.
7. Under the *assumed-for-contradiction* global order-`2m` estimate, derive
   (30) from `Y = π j h + h η(Y)`, continuity, and the vanishing order of
   the symbol. `d_(2m)(0)` is included already in `g(Y)`.
8. Formalize the established inverse-kernel limit (26), diagonal trace
   passage and integral (27)–(29), dominated trace passage (31), and
   the arithmetic contradiction (32)–(33). The spectral-limit premise is
   conditional on the global estimate, not an unconditional conflicting limit.

## Assembly milestones (20 September 2026)

`DeterminantRemainder.lean` now supplies the actual Lemma 3 statements:
the normalized determinant equals the sine plus the concrete finite remainder;
that remainder is real and regular; it gives the exact eigenvalue criterion;
its value and derivative have uniform exponential bounds; and its value at pi
is zero with the endpoint improvement (12). The individual local run is
`evidence/logs/determinant-remainder-02.json`; the latest integrated run record
states separately whether it includes this module. No earlier spectral
estimate is assumed in these declarations. Independent review applies only
to the scopes and source hashes stated in `reviews/`.

This completes the determinant-remainder construction. Later source-matched
component checks below establish the remaining steps. The final TargetProof
assembly now discharges all its prerequisites. Helpers do not add distinct
original problems.

Further actual local components establish the strict spectral enclosure,
unique simple roots in each high phase window, absence of interior roots
in the final phase window, and no-gap coverage. `PhaseWindowIndexing.lean`
now discharges the finite counting hypotheses for the actual spectrum,
identifying each high phase label with its original one-based index.
The quantitative phase-preimage bounds now follow in PhaseQuantitative.
The actual uniform implicit phase, one derivative-defined Taylor family,
coefficient vanishing, its identification with those exact phase preimages,
and spectral error (25) are assembled in ImplicitSpectralData.
The actual Toeplitz inverse and its finite entries
follow from the weighted binomial identity and two-sided triangular inverses;
its reversal symmetry is also proved. InverseKernelLimit now establishes
the concrete uniform limit on the entire closed square, retaining the
ceiling indices and both one-cell shifts. ActualKernelDiagonal and
ActualTraceLimit identify its diagonal and prove the rational matrix
trace limit (29), including the n+2 normalization.

CirculantOrder, DiagonalInterlacing, HermitianInterlacing and CirculantBounds
now prove increasing enumeration and actual interlacing (21)–(22), including
the fixed-prefix upper bound and reciprocal summable majorant. ExpansionAssembly
proves the global and bulk estimates; InverseSpectralTrace and SpectralTracePassage
prove the exact finite identity and dominated passage (31). ActualFixedIndex
supplies the critical fixed-index limit for every original j >= 1.
ExtensionIndependence proves equality under arbitrary smooth extensions,
including both endpoints. TargetProof combines these actual results into the
canonical Target and the same-family C-infinity manuscript theorem.
The exact independent source and execution scopes remain in VERIFICATION.md
and reviews/. A local complete theorem is not a claim that Comparator has run.

## First numerical statement selected before proof

The elementary sign margin used in Lemma 4 is
`1/4 < sin(pi/4) = sqrt(2)/2`. This can be reduced to a single closed
algebraic square-root inequality for kernel-mode LeanCert. No matrix-size
enumeration, parameter subdivision, or numerical assumption is needed.

## First analytic statement selected before proof

Let `h_n → 0` be positive eventually, `y_n → 0`, and `η` continuous at zero.
If eventually `y_n = b h_n + h_n η(y_n)`, then
`y_n / h_n → b + η(0)` and
`g_m(y_n) / h_n^(2m) → (b + η(0))^(2m)`.
If additionally `|λ_n - g_m(y_n)| ≤ C h_n^(2m+1)` eventually,
then the same limit holds for `λ_n / h_n^(2m)`.
For the manuscript's `b = π j` and `η(0) = (m-1)π/2`, this is exactly
equation (30). These are analytic lemmas with explicit earlier hypotheses;
they do not themselves prove that the Toeplitz eigenvalues meet the hypotheses.
