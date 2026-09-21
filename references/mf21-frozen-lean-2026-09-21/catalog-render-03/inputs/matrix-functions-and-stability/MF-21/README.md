# MF-21 — The uniform expansion threshold for Toeplitz symbols with higher-order zeros

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Lean verified

**Last checked:** 2026-09-20

**Rating rationale:** Matching bulk asymptotics with extreme eigenvalues at the exact breakdown order is challenging; the detailed expansion threshold is mainly important to structured spectral specialists.

## Lean proof and verification evidence — 20 September 2026

The [complete formalization](lean/README.md) proves all three original assertions for every $`m\ge3`$, the obstruction for every continuous coefficient family, and the revised proof's smooth common family with matching upper and finite-head lower error bounds. The exact Fourier-integral matrix correspondence and coefficient uniqueness are separately exported. No analytic or transcendence hypothesis remains unproved in these results.

The immutable local proof commit `e378ec4679f9119aacf79a0fe30b80493a61ec5b` passed the actual non-root Linux Comparator, Lean default-kernel replay, standard-axiom checks, and real sandbox/rejection controls. [Checked input snapshot and raw evidence](lean/verification/linux-2026-09-20/README.md) · [Five proved exports](lean/Solution.lean) · [Exact statement correspondence](lean/NUMERICAL_TARGETS.md).

Separate nonimplementing AI agents approved the [formal statement and source correspondence](lean/reviews/independent-fidelity.md) and [proof and runtime evidence](lean/reviews/independent-proof.md); an additional [scoped cross-review](lean/reviews/independent-cross-review.md) records authorship exclusions. The formalization and September proof revisions were produced by OpenAI Codex AI agents. George Stepaniants retains original manuscript authorship, and the conjecture and simple-loop method retain the cited authors' attribution. No external human peer review or source-author endorsement is claimed. Verification was completed locally before the authorized publication in [PR #309](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/309).

## Independent formalization of the frozen manuscript

An [additional Lean formalization](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/fe2183e9b570322d7c1f64bba3480460082af8d3/matrix-functions-and-stability/MF-21/lean-frozen-2026-09-12) follows the unchanged manuscript from commit `eb37bc17`. Its `MF21Restart.Contracts.target_proved` and `MF21Restart.Contracts.manuscript_smooth_target` prove the original three-part target with one smooth coefficient family. The development retains the original boundary determinant, phase indexing, inverse-kernel limit, and trace contradiction. It supplements the existing formalization and does not add another distinct solved problem.

Local checks cover all 125 source files and 386 axiom reports, using only the permitted standard foundational axioms. After the full build, the final phase-source adjustment was checked by recompiling its 10 affected modules and validating 115 unchanged outputs for reuse. Lean 4.33.1, Mathlib and kernel-mode LeanCert are pinned in the [proof project](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/fe2183e9b570322d7c1f64bba3480460082af8d3/matrix-functions-and-stability/MF-21/lean-frozen-2026-09-12); it includes exact statements, component reviews and two additional nonimplementing final referees, and the one-process reproduction command `python3 verify_local.py`. The [separate Linux run](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35552653565) and [retained publication evidence](../../references/mf21-frozen-lean-2026-09-21/README.md) identify the exact checked revision and the actual Comparator, kernel-replay and sandbox results. George Stepaniants is credited with his Department of Computing and Mathematical Sciences, California Institute of Technology affiliation, with substantial AI assistance disclosed.

## Proof clarification - 19 September 2026

The [revised proof](solution.md) explicitly proves uniqueness of the continuous coefficient functions on the logarithmic-squared bulk grid (Lemma 5, following Proposition 4.2 of Barrera–Böttcher–Grudsky–Maximenko). This identifies any hypothetical all-index expansion with the constructed one. Equation (25) supplies only an upper bound; the obstruction uses the separate inverse-trace contradiction in equations (26)–(33). Corollary 6 now gives a matching lower bound of order $`h^{2m}`$ for the maximum error over a fixed finite set of low indices.

The revision also credits the simple-loop method explicitly and adds Bogoya–Grudsky (2025). The [dated audit](../../reviews/2026-09-19-mf21/README.md) records the mathematical checks, source comparison, and coefficient-uniqueness repair. The [initial Lean audit](../../reviews/2026-09-19-mf21/lean-audit.md) records the earlier partial development; it is superseded by the completed verification above. The original problem, permanent ID, grid, cutoff, and quantifiers below are unchanged.

## Affirmative resolution - 12 September 2026 (UTC)

**Author:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA.

[Theorem 1 and Sections 2-5 of the complete proof](solution.md) establish all three assertions below for every integer $`m\ge3`$, using the same smooth coefficient functions with $`d_0=g_m`$. The expansion is uniform over every eigenvalue through order $`2m-1`$, extends to order $`2m`$ above the stated logarithmic-squared index cutoff, and fails to extend uniformly to all indices at that order. The matrix, grid normalization, parameter quantifiers and cutoff are unchanged.

[Proof PDF](solution.pdf) · [Standalone proof TeX](solution.tex) · [Independent mathematical review](../../references/stepaniants-mf21-2026-09-12/independent-review.md) · [Submission and public-source audit](../../references/stepaniants-mf21-2026-09-12/README.md).

The original proof passed a separate Codex-agent informal audit. It derived the bulk expansion from an exact boundary determinant and the final obstruction from a classical uniform inverse-kernel limit and a trace identity; the revision above supplies a direct finite-matrix trace calculation. Barrera, Böttcher, Grudsky, Maximenko and the cited later authors retain credit for the conjecture and prior cases; Böttcher-Widom and their cited predecessors retain credit for the inverse-kernel theorem. Substantial AI assistance is disclosed. That initial audit was informal; the completed Lean verification is documented above. External human peer review is not claimed. The original statement, permanent ID, references and dated history are retained below; the ratings are historical.

## Statement

For each integer $`m\ge3`$, let

```math
g_m(\theta)=\bigl(2\sin(\theta/2)\bigr)^{2m},\qquad
\widehat g_{m,k}=\frac1{2\pi}\int_{-\pi}^{\pi}g_m(\theta)e^{-ik\theta}\,d\theta.
```

Let $`T_n(g_m)=(\widehat g_{m,j-k})_{j,k=1}^n`$, with eigenvalues $`\lambda_{n,1}\le\cdots\le\lambda_{n,n}`$ counted with multiplicity. For real continuous functions $`d_0,\ldots,d_{2m}`$ on $`[0,\pi]`$, independent of $`n,j`$, write

```math
R_{p,n,j}=\lambda_{n,j}-\sum_{k=0}^p
\frac{d_k(j\pi/(n+2))}{(n+2)^k}.
```

**Conjecture 8.4 of Barrera–Böttcher–Grudsky–Maximenko.** Such coefficient functions exist, with $`d_0=g_m`$, for which all three assertions hold:

1. For every integer $`0\le p\le2m-1`$, there are constants $`D_p>0`$ and $`N_p\in\mathbb N`$ such that

   $`\displaystyle |R_{p,n,j}|\le D_p(n+2)^{-p-1}\qquad(n\ge N_p,\ 1\le j\le n).`$

2. There are constants $`D_{2m}>0`$ and $`N_{2m}\in\mathbb N`$ such that

   $`\displaystyle |R_{2m,n,j}|\le D_{2m}(n+2)^{-2m-1}`$

   whenever $`n\ge N_{2m}`$ and $`\lceil(\log(n+2))^2\rceil\le j\le n`$.
3. No constants $`D>0,N\in\mathbb N`$ make the bound $`|R_{2m,n,j}|\le D(n+2)^{-2m-1}`$ valid for every $`n\ge N`$ and every $`1\le j\le n`$.

All constants may depend on $`m`$ and the expansion order; $`\log`$ denotes the natural logarithm. The same coefficient functions are used throughout. The continuity and existence quantifiers make explicit the regular-expansion convention of the source's Theorem 1.2 and §8; these are not matrix-size-dependent fitted coefficients.

## Numerical significance

Regular eigenvalue expansions support accurate computation without forming large Toeplitz matrices. This conjecture identifies exactly where extreme eigenvalues obstruct a uniform expansion for these polynomial symbols. It retains all three parts as one problem.

## References and status check

- M. Barrera, A. Böttcher, S. M. Grudsky and E. A. Maximenko, *Eigenvalues of even very nice Toeplitz matrices can be unexpectedly erratic*, Oper. Theory Adv. Appl. **268** (2018), 51–77, [DOI](https://doi.org/10.1007/978-3-319-75996-8_2); [author preprint](https://arxiv.org/abs/1710.05243), Conjecture 8.4, p. 26, equation (8.4); Theorem 1.2 supplies the proved $`m=2`$ analogue.
- M. Barrera, S. Grudsky, V. Stukopin and I. Voronin, *Asymptotics of the eigenvalues of seven-diagonal Toeplitz matrices of a special form*, Adv. Oper. Theory **9** (2024), 79, [DOI](https://doi.org/10.1007/s43036-024-00374-1); [preprint](https://arxiv.org/abs/2111.07196), Theorems 2.3–2.6. This studies the sixth-order-zero case with more elaborate formulas.
- M. Bogoya and S. Grudsky, *Eigenvalues of non-Hermitian banded Toeplitz matrices approaching simple points of the limiting set*, Comput. Math. Math. Phys. **65** (2025), 1453–1471, [DOI](https://doi.org/10.1134/S0965542525700745); [author-hosted paper](https://www.math.cinvestav.mx/~grudsky/Papers/162.pdf), Theorems 2.1–2.2. This gives local phase equations and expansions near nondegenerate simple points; the revised proof records the methodological connection without a novelty claim.
- A. Böttcher, *Ten years with Sergei Grudsky in the eigenvalue bulk of Toeplitz matrices*, J. Math. Sci. **298** (2026), 363–376, [DOI](https://doi.org/10.1007/s10958-025-07833-x), section “Beyond the simple-loop class,” Theorems 2–5 and discussion of higher-order zeros.

On 2026-09-10, checked the original full preprint, the seven-diagonal follow-up's full preprint and publication record, the 2026 survey, and targeted title/conjecture/2025–2026 searches. No resolution of all parts for every $`m\ge3`$ was located. Later local second-order expansions and results confined to $`m=3`$ do not establish this full statement. This bounded search is not a proof of openness.

## Audit — 2026-09-10

Independently rechecked [Conjecture 8.4](https://arxiv.org/pdf/1710.05243), [the seven-diagonal paper's Theorems 2.3–2.6](https://arxiv.org/pdf/2111.07196), and [Böttcher's survey](https://doi.org/10.1007/s10958-025-07833-x). Corrected the status to Open: the proved $`m=2`$ analogue lies outside the displayed range, and the $`m=3`$ local and second-order formulas do not establish the three-part threshold assertion. The [March 2026 eigenvalue-superposition paper](https://doi.org/10.1007/s10958-026-08227-3) assumes simple-loop symbols, excluding these higher-order zeros. Title and conjecture searches found no complete resolution. Challenging difficulty and specialist importance are retained.

## Resolution audit - 2026-09-12

The independent audit checked the complete all-$`m`$ argument, including the coalescing characteristic roots, normalized determinant remainder, upper-endpoint cancellation, eigenvalue indexing, all three expansion orders, and dominated trace limit. The primary-source and public branch/fork/PR checks found no existing full resolution at the recorded time; the linked submission record gives the precise scope and limitations of that search.
