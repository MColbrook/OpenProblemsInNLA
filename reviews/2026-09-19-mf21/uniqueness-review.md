# MF-21: independent review of the coefficient-uniqueness supplement

Date: 19 September 2026. Reviewer: independent Codex subagent `/root/trace_audit`.

Reviewed file: [uniqueness-supplement.md](uniqueness-supplement.md).
Reviewed SHA-256: `c26582c684dd982e674e7949ac49e3d34dbcff131b31b24ed2882acca4cc40a1`.

**Verdict: PASS. The elementary uniqueness proof and its application are valid. No mathematical correction is required.** This is an informal review, not formal verification.

## Proof checks

1. For each fixed interior point `0<x<π`, the floor choice satisfies
   `j_n/(n+2)→x/π`. The cutoff satisfies `ceil(log(n+2)^2)/(n+2)→0`.
   Since `x/π` lies strictly between zero and one, the inequalities
   `1≤ceil(log(n+2)^2)≤j_n≤n` hold for all sufficiently large `n`.
   The additive two in the denominator does not change this conclusion:
   `n/(n+2)→1`, leaving a positive upper margin for every fixed `x<π`.

2. Both expansion estimates therefore apply to the same eventual sampling
   sequence and the same eigenvalue. Their difference is bounded by the sum
   of their constants times `h_n^(p+1)`. Sampling points tend to `x` and stay
   in the interval on which continuity and boundedness are assumed.

3. At induction stage `k`, the preceding coefficients have already been
   proved equal on the *whole interval*, not just at the current limiting
   point. This correctly makes every lower-order term vanish at every
   sampling point. Dividing by `h_n^k` is valid because `h_n>0`.

4. The finitely many higher coefficient differences are bounded by compactness.
   Their terms contain strictly positive powers of `h_n` and tend to zero.
   The remainder tends to zero because `p+1−k≥1`. Continuity identifies the
   remaining limit with `(d_k−e_k)(x)`, forcing equality.

5. The argument applies to every interior point; continuity then extends
   equality to both endpoints. Establishing closed-interval equality at
   each induction stage makes the induction sound. For `k=0`, the lower
   sum is empty. For `k=p`, the upper sum is empty. The case `p=0` is also
   covered.

Only the top-order expansion estimate is needed. Lower-order estimates are
not hidden hypotheses: higher coefficients disappear by boundedness after
division, exactly as the supplement states.

## Application and relation to the original target

Any continuous family with a global order-`2m` expansion also gives that
expansion on the smaller logarithmic-square bulk index set. The constructed
family gives the same-order expansion there by the manuscript's Part 2.
The lemma identifies the two families on the entire closed interval. The
Section 5 contradiction for the constructed family thus excludes every
continuous alternative family.

This is a sufficient repair for the stronger reading of the obstruction;
no differentiability of a hypothetical family is required. It also does
not require a hypothetical family to satisfy every lower-order estimate
separately, or to stipulate `d_0=g` in advance: uniqueness forces all of its
coefficients to equal the constructed ones.

The canonical three-part formulation asserts existence of one common
continuous coefficient family satisfying the two positive expansion claims
and the negative claim for that same family. Logically, failure for that
family alone is a weaker negative statement than failure for every family.
The uniqueness lemma shows that, once the bulk existence statement is
available, these formulations have the same obstruction: no alternative
continuous coefficients can avoid it. It is therefore appropriate to
present uniqueness explicitly, rather than silently substitute a stronger
negative quantifier in the problem statement.

This is consistent with [Barrera–Böttcher–Grudsky–Maximenko,
Proposition 4.2 and Remark 8.3](https://arxiv.org/pdf/1710.05243). Their
uniqueness principle supplies the same bridge in the earlier `m=2` case;
the supplement proves the specialization needed here directly.

## Scope of the current Lean helper

I also inspected `lean/CoefficientUniqueness.lean`. Its coefficient extraction
and generic mesh theorem faithfully state narrower helper results. The
generic theorem explicitly assumes all truncation estimates, convergence and
membership of the supplied mesh, and ambient `ContinuousAt` hypotheses. It
does not yet formalize the logarithmic-square mesh argument, the deduction
from only a top-order estimate, or the closed-interval endpoint step. These
differences are documented in the Lean file and are not evidence that the
full MF-21 theorem or the full supplement has been formally verified.

No canonical source, problem statement, or problem registry was modified.
