# MI-27 — Constant one in the logarithmic commutator inequality

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** broadly interesting  
**Status:** Lean verified
**Last checked:** 2026-09-19

**Historical rating rationale:** Improving the known universal coefficient to its proposed sharp value is challenging; connections between matrix logarithms, entropy and quantum dynamics make the question broadly interesting.

## Resolution: affirmative, 12 September 2026

**Sidney Holden**, Center for Computational Biology, Flatiron Institute, Simons Foundation,
proves the exact inequality for every dimension and every complex positive definite
pair in the original statement, with optimality already in order two.
See **Theorem 1.1, Sections 2–5**, of the [complete manuscript](../../references/holden-mi27-2026-09-12/solution.pdf)
([Markdown](../../references/holden-mi27-2026-09-12/solution.md), [LaTeX](../../references/holden-mi27-2026-09-12/solution.tex)).

A [separate Codex AI-agent audit](../../references/holden-mi27-2026-09-12/verification/independent-review.md)
passed the full proof and checked its published relative-entropy input.
That review was informal; the later Lean verification is recorded below. No external human peer review or priority claim is asserted.
[Provenance and verified affiliation](../../references/holden-mi27-2026-09-12/provenance.md)
disclose AI assistance and credit [PR #186](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/186),
whose partial results left the universal upper bound open.
The original target below is retained; ratings above are historical.

## Lean proof and verification evidence

**The complete original coefficient-one bound is Lean verified, 19 September 2026.** The [immutable proof source](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/1f05b398013d44beb7d756cbfbbfd3e875c8deab/matrix-inequalities-and-norms/MI-27/lean/Solution.lean) passed [non-root Linux run 35438172834](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/35438172834). The actual PR merge checkout was `f21284e35e8156a9761c1f2ccd49d579f42fb69a`; all 284 submitted project inputs match PR head `1f05b398013d44beb7d756cbfbbfd3e875c8deab`. [Retained logs and source authentication](lean/verification/linux-2026-09-19/README.md) record real Comparator statement matching, Lean default-kernel replay, standard transitive axioms, sandbox checks and rejection controls for all twenty frozen contracts. Subsequent publication changes are checked separately.

The main declaration `NLA.MI27.logarithmic_commutator_bound` proves the unchanged target for every positive dimension and every complex positive definite pair with trace sum one, using the natural spectral logarithm and the full Gram-square-root trace norm. It has coefficient exactly one and no added commutativity, spectral, entropy-identity or differentiability hypothesis. The ordinary noncommuting relative-entropy identity and the trace-entropy derivative are proved internally. The manuscript's separate order-two optimality result is outside this formalization.

Formalization: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology, with substantial OpenAI Codex assistance. **Sidney Holden** retains credit for the analytic resolution; Audenaert, Kittaneh, Frenkel, Hirche, Tomamichel and the library/source authors retain their respective credit. Two independent nonauthor AI-agent final reviews approved the full source: [referee B](lean/reviews/final-referee-b/REPORT.md) and [newmath referee](lean/reviews/final-newmath/REVIEW.md). This does not claim external human peer review or official Tau Ceti service execution.

The [standalone project](lean/README.md) pins Lean 4.33.1, Mathlib and LeanCert. Kernel-mode LeanCert proves only the exact positivity of one half, used in the positive-commutator argument; the matrix and integral arguments are symbolic. All twenty exports have only `propext`, `Classical.choice` and `Quot.sound` as transitive axioms. The seven reused MI-24 support modules do not count as another completed problem. The original statement, ID and canonical path remain unchanged.

## Earlier supporting results — 12 September 2026

Holden's [Theorems 1 and 2](../../references/holden-matrix-2026-09-12/MI-27/result.md) established projection equivalence and a strictly positive order-two sharpness family. The [independent review](../../references/holden-matrix-2026-09-12/verification/MI-20-MI-27-review.md) remains available. Those results left the universal upper bound open; the full proof above supplies it.

## Problem statement

For every integer $`n\ge1`$ and positive definite $`A,B\in\mathbb C^{n\times n}`$ with $`\mathop{\mathrm{tr}}\nolimits(A+B)=1`$, set $`a=\mathop{\mathrm{tr}}\nolimits A`$, $`b=\mathop{\mathrm{tr}}\nolimits B`$. Is

```math
\bigl\|B\log(A+B)-\log(A+B)B\bigr\|_1
\le -a\log a-b\log b
```

always true? The logarithm is the natural logarithm applied by spectral functional calculus; $`\|X\|_1=\mathop{\mathrm{tr}}\nolimits(X^*X)^{1/2}`$. Thus $`a,b>0`$ and $`a+b=1`$, and every expression is well-defined.

The target is specifically the coefficient $`1`$ on the right. Existence of some dimension-independent coefficient has been proved and is not the open question. The coefficient-one question is explicitly suggested immediately after the original displayed conjecture.

This is a sharp matrix-function estimate for the rate at which noncommuting positive matrices mix. It connects perturbation estimates for the matrix logarithm with entropy production and quantum information.

## References

1. K. M. R. Audenaert and F. Kittaneh, *Problems and Conjectures in Matrix and Operator Inequalities*, arXiv:1201.5232v3 (2012), §6, Conjecture 4, equation (26), and the sentence proposing $`c=1`$. [Full text](https://arxiv.org/html/1201.5232).
2. K. M. R. Audenaert, *Quantum Skew Divergence*, J. Math. Phys. 55 (2014), 112202, §8, proof of small incremental mixing with coefficient $`2`$. [Full text](https://arxiv.org/html/1304.5935).
3. A. Vershynina, *Entanglement rates for Renyi, Tsallis and other entropies*, arXiv:1803.07117v3 (2021), §8, conclusion, pp. 15–16, explicitly distinguishing the proved coefficient $`2`$ and proposed coefficient $`1`$. [Full preprint](https://arxiv.org/pdf/1803.07117).

4. Q. Ning, F.-Z. Guo, J. Zhang and Q.-Y. Wen, *On Bounding Entangling Rates and Mixing Rates in Some Special Cases*, Int. J. Theor. Phys. 55 (2016), 1686–1694. [Published abstract](https://doi.org/10.1007/s10773-015-2806-9), which reports coefficient one under additional restrictions; the subscription body was not independently inspected in this audit.

Historical status check (2026-09-10; superseded by the resolution above): Audenaert's theorem settles the existence claim with $`2`$. Vershynina’s 2021 revision distinguishes the proved coefficient from the proposed coefficient $`1`$. Searches for “small incremental mixing sharp constant”, “logarithmic commutator Audenaert constant one”, and 2025/2026 found later special-case estimates but no announced universal coefficient-one proof or counterexample. This limited search does not certify that the conjecture remains open.
