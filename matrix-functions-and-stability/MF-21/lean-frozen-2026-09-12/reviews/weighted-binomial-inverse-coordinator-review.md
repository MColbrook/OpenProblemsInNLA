# Review of the finite weighted binomial identity

Verdict: **APPROVE**, restricted to the three public declarations in
`MF21Restart/WeightedBinomialInverse.lean`. This is a coordinator review of
source written by `/root/mf21_restart_lean_audit`. The coordinator discussed
and independently checked the telescoping identity before implementation;
this is not a claim of a blind review or external human peer review.

The reviewed source SHA256 is
`cf95e7dc24c3e50e41c45c3fbd15f00200ac3c1203ae6e7fa28b6ed3e6d0324e`.
The prior statement/proof lock is `WEIGHTED_BINOMIAL_INVERSE_STATEMENTS.md`,
SHA256 `f64a669fc926c1f87bc8390d7826c4ebbac65da24db22bd6b0ea182f773b78b4`.
The actual local test is `evidence/logs/weighted-binomial-inverse-02.json`
with its corresponding log. The coordinator recomputed and matched the
recorded source, log and output hashes. The run returned exit 0 using
`LEAN_NUM_THREADS=1 lake env lean -j1 -M4096 -o
.lake/build/lib/lean/MF21Restart/WeightedBinomialInverse.olean
MF21Restart/WeightedBinomialInverse.lean`. All three printed declarations
use only `propext`, `Classical.choice` and `Quot.sound`. The failed first
development run is not evidence of success. Comparator has not run.

The recurrence is proved for every real x, with no division by x or x-r.
The certificate is
`G(r)=-r(d+r)*choose(m,r)*choose(m,d+r)*(x+1-r)_(2m)`.
Its forward difference equals the desired weighted summand difference.
The two essential polynomial factors are
`x(x+d)-r(r+d)=(x-r)(x+r+d)` and
`(x+m)(x+m+d)-(m-r)(m-d-r)=(x-r+2m)(x+r+d)`.
The rising-factorial shift identity and consecutive choose identity then
give the certificate, including the sign. Both boundary terms vanish:
one contains r=0, the other an out-of-range binomial coefficient.

At x=1 every summand with r>=1 has an actual zero of the ascending
Pochhammer polynomial. The factorial expression for the remaining term
matches the proposed right side using nonzero natural factorials. Induction
uses x=j+1>0 and x+d>0 before cancellation; it does not divide at a root.
Equality on all real x is obtained from equality of two explicit polynomials
at infinitely many distinct positive integers. Neither sampling nor an
unproved interpolation hypothesis supplies this equality.

The one-based sum uses k in Icc(1,j), with i=j+d and j>=1. Reindexing by
r=j-k is bijective on the stated ranges. Extra terms vanish either by an
out-of-range binomial coefficient or a negative-integer Pochhammer root.
Natural subtraction is guarded by the relevant order hypotheses. The d>m
case is handled separately, with both sides zero. The endpoint d=m reduces
to a singleton nonzero term and is included. No negative offset is silently
converted to truncated natural subtraction.

This proves symbolic finite algebra toward the known Duduchava–Roch
formula, with attribution retained. It does not identify the actual Fourier
Toeplitz coefficients with the binomial stencil, invert a finite matrix,
prove uniform kernel convergence, or identify the limiting trace. Those
obligations remain. There is no new solved-problem or completed MF-21 count.
