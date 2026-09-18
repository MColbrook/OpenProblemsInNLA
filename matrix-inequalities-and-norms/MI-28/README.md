# MI-28 — Ghabries's determinant comparison for arbitrary nonnegative base powers

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Lean verified  
**Last checked:** 2026-09-18

**Rating rationale (historical):** The intermediate base powers resist the available determinantal comparisons, making the problem challenging; the immediate application is to specialist matrix-function inequalities.

## Resolution — 2026-09-11

**Solved (affirmative).** George Stepaniants's [complete proof](solution.md), **Theorem 1 and Corollary 6**, proves the displayed determinant inequality for every dimension, every complex positive definite pair, all $`k\ge0`$ and all $`0\le p\le2`$. It proves the stronger log-majorization of the corresponding normalized matrices. The proof credits Ghabries–Abbas–Mourad–Assi's published result for $`k\ge2`$ and establishes the remaining range using Furuta inequalities and a parameter interchange. [Proof PDF](solution.pdf) · [Standalone TeX](solution.tex).

The full analytic argument passed a [separate Codex-agent review](../../references/stepaniants-mi28-2026-09-11/verification/reviews/MI-28-review.md), including every exponent restriction, the noncommuting factor order, exterior powers, endpoints and exact source substitutions. It was developed with ChatGPT/Codex; that September 11 verification was independent agent review. The later Lean verification is recorded below; no external human peer review is claimed. [Authorship, source checks, reproduction and public-branch audit](../../references/stepaniants-mi28-2026-09-11/README.md). The original ID, path, target, historical ratings and earlier status check below are retained.

## Lean proof and verification evidence

**The complete original target is Lean verified, 2026-09-18 (UTC).** The [immutable proof](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/aae2941f9a7f1e28b8010f5216574d93bdc72181/matrix-inequalities-and-norms/MI-28/lean/Solution.lean) at revision `aae2941f9a7f1e28b8010f5216574d93bdc72181` passed [non-root Linux run 35374928604](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35374928604/job/105697400237). The [retained execution evidence](lean/verification/linux-2026-09-18/README.md) binds all 282 submitted project inputs and 20 exported statements. Real Comparator, default-kernel replay, standard transitive axioms, sandbox checks and rejection controls passed. Later publication and PR merge checkouts are checked separately.

The main declaration `NLA.MI28.determinant_comparison` proves the unchanged determinant inequality for every positive dimension, all complex positive definite matrices, every real nonnegative base power and the full closed power interval in the original statement. `NLA.MI28.full_log_majorization` proves the stronger normalized comparison. Both determinant reality and positivity are proved, including for the non-Hermitian right matrix. Powers and modulus use concrete spectral functional calculus; no commutativity, spectral gap or upper bound on the base power is assumed. Zero exponents, both interval endpoints and every exterior degree are included. The [20 exact contracts](lean/Challenge.lean) and [proof map](lean/PROOF-REVIEWER-MAP.md) identify all definitions and assumptions. Furuta and the large-base comparison are proved internally, with prior mathematical credit retained; no cited theorem is a Lean axiom.

Mathematical resolution and formalization: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology. The original question and prior results of Ghabries, Abbas, Mourad and Assi, and Furuta, Fujii and Tanahashi background retain their attribution. Two independent statement reviews preceded implementation; two independent nonauthor final reviews approved the full 52-module proof closure, including 18 unchanged, credited MI24 modules. The [review records](lean/REVIEW-INDEX.md) disclose substantial ChatGPT/Codex assistance and distinguish source review from actual execution.

The project pins Lean 4.33.1, [Mathlib](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) and [LeanCert](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926). Kernel-mode LeanCert certifies the fixed half-exponent used by the modulus-square argument; the matrix and unbounded-parameter reasoning is symbolic. All exports use only `propext`, `Classical.choice` and `Quot.sound`. Run `lake build Solution` in `matrix-inequalities-and-norms/MI-28/lean`; [reproduction instructions](lean/README.md) distinguish local compilation from the genuine Linux checker.

## Problem statement

For every integer $`n\ge1`$, positive definite matrices $`A,B\in\mathbb C^{n\times n}`$, and real parameters $`k\ge0`$, $`0\le p\le2`$, determine whether

```math
\det(A^k+|AB|^p)\ge\det(A^k+A^pB^p)
```

holds. Here $`|AB|=((AB)^*(AB))^{1/2}`$, and powers are defined by spectral functional calculus; the zeroth power of a positive definite matrix is the identity. Although the matrix inside the determinant on the right need not be Hermitian, its determinant is a positive real number: factor out $`A^k`$ and use that a product of two positive definite matrices has positive eigenvalues.

The source states the conjecture for positive semidefinite inputs. The positive definite formulation captures the nontrivial question and avoids ambiguity in zeroth powers; positive-exponent semidefinite cases follow by regularization.

Such determinants arise in comparisons of interpolants for positive definite data. The distinction between a product's modulus and the product of matrix powers is important in matrix-function inequalities.

## References

1. M. M. Ghabries, *Contributions to Matrix Inequalities and Some Applications*, PhD thesis, University of Angers and Lebanese University (2022), §2.5 and final Open Problems, Problem 1, pp. 109–110. [Thesis uploaded by its author](https://www.researchgate.net/publication/361793582_Contributions_to_Matrix_Inequalities_and_Some_Applications).
2. H. Abbas, M. M. Ghabries and B. Mourad, *New determinantal inequalities concerning Hermitian and positive semi-definite matrices*, Operators and Matrices 15 (2021), 105–116, §4, Conjecture 2, p. 116 (earlier, narrower parameter region). [Publisher PDF](https://files.ele-math.com/articles/oam-15-07.pdf).
3. M. M. Ghabries et al., *A proof of a conjectured determinantal inequality*, Linear Algebra Appl. 605 (2020), 21–28, main theorem. [Publisher](https://doi.org/10.1016/j.laa.2020.07.013).

Status check (2026-09-10): the thesis retains the range $`0< k<2`$, $`0< p<2`$, after recording proved results for $`k\ge2`$ and for $`p=2`$. Its broader question supersedes the 2021 formulation. The 2020 resolution concerns Lin's earlier $`k=2`$ question. The author's July 2026 normal-matrix determinant paper and searches for “Ghabries determinant arbitrary k conjecture”, exact titles, and 2025/2026 yielded no full resolution. This is a bounded check.
