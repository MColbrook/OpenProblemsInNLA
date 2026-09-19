# PR 302 / MF-08 supplemental audit

2026-09-19. Read the retained target and complete proof, Sections 1–6 and Appendix A, of [Löfberg, arXiv:2609.16886v1](https://arxiv.org/html/2609.16886v1). No substantive gap found; supports merging. Informal AI analysis, without formalization or computational reconstruction. The other cited paper was outside this supplemental assignment.

- **Applicability:** integer single-input instances embed into the rational-input language through denominator-one encoding. The gain remains unrestricted and real; stability remains strictly Hurwitz. This is a polynomial many-one reduction, not a bounded-gain or pole-placement substitute.
- **Frequency separation:** checked the relative-error identity and constants. Full disks account for every root; strict half-disk boundary comparisons exclude imaginary-axis roots. The argument uses fixed baseline roots when estimating distant factors.
- **Unbounded gains:** selecting a maximal-magnitude coordinate makes its anchor dominate near its positive perturbation root. The selected ratio decreases as inverse gain magnitude, cancelling the distant sum's linear growth. The resulting strict bound is uniform beyond the auxiliary box, including negative gains. No bounded-source root estimate is reused improperly.
- **Binary size/realization:** fixed-degree integer formulas give polynomial magnitude. Direct realified companion blocks avoid expanded-polynomial coefficient inflation. The output sign and factor two give the required characteristic-polynomial identity by the rank-one determinant lemma.

The retained problem is settled by this reduction; this audit does not establish journal acceptance, external human review, or priority.
