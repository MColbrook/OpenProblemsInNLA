# MF-21 audit following author correspondence

19 September 2026. This directory contains technical audit work by Codex.
It contains no email reply and no correspondence intended for sending.

## Completed local verification

The local revision branch is `codex/mf21-proof-corrections`, based on
`origin/main` at `bd3f7a055e1376c573ef9036124a86833641f9f1`. The revised
manuscript incorporates the uniqueness proof, the finite-index lower bound,
and the attribution corrections. The revised PDFs are rebuilt from the updated sources. The complete Lean
verification has now passed, including independent source review and actual
isolated Linux Comparator acceptance. Explicit user permission remains
required before any push.
No push or GitHub PR creation has occurred.

The sections below record the original audit snapshot. The later formal
progress is recorded separately in [formalization progress](formalization-progress.md).
As of 20 September, the complete theorem, universal-family obstruction,
smooth common family, sharp finite-head/global bounds and Fourier bridge
have passed a fresh raw-kernel source replay. The canonical project is
[MF-21/lean](../../matrix-functions-and-stability/MF-21/lean/README.md).
The isolated Linux Comparator and two independent nonimplementing final
canonical reviews have passed; the accepted proof revision and all evidence
are linked from the canonical project.
The incomplete-status discussion below is historical and is superseded by
the dated progress record; it is not a description of the current proof code.

## Findings in the initial audit

The current published argument is not refuted by the observation that
equation (25) is only an upper bound. That observation is correct, but the
manuscript uses the separate trace contradiction in equations (26)–(33) to
exclude a uniform error of order $h^{2m+1}$. Independent informal checks of
the determinant and expansion argument and of the trace argument found no
mathematical error in those parts, subject to the explicitly cited classical
inverse-kernel theorem. This is not external human peer review.

The manuscript omits the coefficient-uniqueness explanation needed to rule
out *any* competing continuous coefficient family. The
[uniqueness supplement](uniqueness-supplement.md) gives the complete argument,
including the logarithmic-square cutoff, and identifies the existing
uniqueness result in Proposition 4.2 of the original conjecture paper.

The method attribution should explicitly include the simple-loop method and
Bogoya–Grudsky (2025). The reports do not assert priority or novelty, or that
the shrinking cutoff follows immediately from a theorem stated only in a
fixed neighborhood of a simple point.

## Evidence

- [Bulk audit](bulk-audit.md): Sections 1–4, determinant, endpoint cancellation,
  eigenvalue indexing, uniform Taylor estimates, and cutoff.
- [Trace audit](trace-audit.md): Section 5, primary-source theorem check,
  diagonal convergence, normalization, domination, and irrationality. Also
  proves an eventual lower bound of order $h^{2m}$ for the maximal error over
  a fixed finite set of low indices.
- [Uniqueness supplement](uniqueness-supplement.md): proof excluding
  alternative continuous coefficient families.
- [Independent uniqueness review](uniqueness-review.md) and
  [cross-review](cross-review.md): separate checks of the uniqueness proof
  and the stronger lower bound.
- [Lean development sources](lean/): partial supporting formalization only.
- [Lean audit and reproduction record](lean-audit.md): checked declarations,
  explicit assumptions, execution evidence, and outstanding proof obligations.
- [First statement review](challenge-statement-review.md) and
  [second statement review](lean-statement-review.md): independent semantic
  checks of the proposed full-target proposition.

## Version check

The working-tree input is at repository commit
`de97a72364055bddb65f23d2da8566e0594b2a8c`. The PDF downloaded on the audit date
from the public `main` branch is byte-for-byte identical to the local PDF:

```text
829d4e48d9ff61869465faf0470f9ff51f50beeee4fab5d46b191c5c4b9a3c8e
```

The PDF has seven pages. Equation (25) is on page 5; Section 5 begins on page
6 and concludes on page 7. Its equations continue through (33). The audit
visually inspected pages 5–7 and checked extracted text against the Markdown
and TeX. This establishes what the public URL serves on the audit date; it
does not establish which file or pages a correspondent actually read.

Other source hashes:

```text
README.md     d7072f0d69da1db6eeb761517bec3bc63f59ba64ebb821caf5a5b7a5609c90a0
solution.md   6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa
solution.tex  1baff64e748b8a3a31d53f1727560937e5c84524a202a25bc92c081b4f1fcd49
```

All refer to `matrix-functions-and-stability/MF-21/` at the initial audit
snapshot, before the local revision and later verified-status update.

## Formal-verification status at the initial audit: incomplete

**The full MF-21 theorem has not been verified in Lean.** The supporting
sources prove only explicitly scoped uniqueness and arithmetic implications.
A conditional contradiction that takes analytic limits as hypotheses does
not establish those limits, and a declaration of a target proposition is not
a proof of that proposition.

The proposed [formal statement](lean-development-source.tar.gz) uses the signed-binomial
Toeplitz matrix and its actual Hermitian eigenvalues, reversed into increasing
order. The equality of those entries to the source's Fourier integral remains
an explicit formal correspondence obligation. The complete original target
and the stronger universal-family obstruction are separate proposition
definitions, neither asserted as a theorem.
This encodes the original continuous-coefficient conjecture. Formalizing
every assertion of the manuscript would also require its stronger smoothness
claim for the constructed coefficients, which this proposition does not assert.

The local development replay uses Lean 4.33.1 with `--trust=0` and mathlib
commit `0df444a360eaa60ab8c11dca51a86af692955474`. It checks the supporting
declarations and their reported axioms. Only `propext`, `Classical.choice`,
and `Quot.sound` occur. The arithmetic contradiction nevertheless has
explicit unproved hypotheses for the analytic limits and transcendence;
these are theorem parameters, which axiom checks do not discharge.
The generic uniqueness theorem likewise assumes its mesh and expansion
estimates; it has not yet been specialized to the MF-21 cutoff.

Outstanding work includes the Toeplitz spectral bridge, stable roots and
boundary determinant, uniform estimates and indexing, construction of the
coefficient functions, the inverse-kernel theorem and diagonal trace limit,
the even-zeta identities and necessary transcendence input, and the complete
assembly with the exact original quantifiers. Repository promotion would
also require statement review and the prescribed fresh Linux Comparator
checks. No `Lean verified` status is claimed here.

## Publication follow-up

After the completed local verification, the user authorized publication. The
verified branch was pushed and [PR #309](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/309) opened. Earlier local-only statements above describe the preparation
phase. No email reply was added to the repository.
