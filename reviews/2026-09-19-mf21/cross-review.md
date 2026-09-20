# MF-21: cross-review of the uniqueness and lower-bound supplements

Date: 19 September 2026. Reviewer: separate Codex agent /root/bulk_audit.

Inputs:

- uniqueness-supplement.md, SHA-256
  c26582c684dd982e674e7949ac49e3d34dbcff131b31b24ed2882acca4cc40a1.
- trace-audit.md, SHA-256
  bddadd406948919a23ceebf967ddc00a63752cb44c7bb99da414a47b3b426127.

**Verdict:** the coefficient-uniqueness proof and the optional fixed-finite-set
lower bound are correct mathematical consequences of their stated hypotheses.
No correction is needed. This is an informal AI review, not formal verification.

## Coefficient uniqueness

The sampling sequence is eventually admissible: its ratio to $n+2$ converges
to a fixed point in $(0,1)$, while the cutoff divided by $n+2$ tends to zero
and $n/(n+2)$ tends to one. The sampled angles converge to the selected
interior point.

Subtracting the two top-order estimates is enough; separate estimates for
all truncations are unnecessary. At each induction step, equality of lower
coefficients has already been proved on the entire closed interval, so those
terms vanish at the moving sample points. Bounded higher coefficients carry
strictly positive powers of $h_n$, and the divided remainder tends to zero.
Continuity proves equality in the interior, then at the two endpoints.
The empty sums at $k=0$ and $k=p$ and the case $p=0$ cause no problem.

Any hypothetical continuous family with a global order-$2m$ estimate gives
the same estimate on the bulk sampling set. Applying uniqueness at $p=2m$
identifies it with the manuscript's family. Thus the trace obstruction for
that family also excludes all continuous competing families. It is not
necessary to assume a competing family is smooth, or that it separately
supplies every lower-order estimate.

## Sharp maximum-error lower bound

The argument in trace-audit.md is independent of an assumed global improved
remainder. Let $s=2m$, $q_{n,j}=\lambda_{n,j}/h_n^s$ and
$b_j=\pi^s(j+(m-1)/2)^s$. The actual reciprocal sum tends to $C_m$,
whereas the comparison reciprocal series sums to $B_m\ne C_m$.

For $j\ge2$, interlacing uniformly bounds $q_{n,j}^{-1}$ by a constant
times $j^{-s}$. Therefore one finite $J\ge1$ makes both reciprocal tails
less than $\delta/8$, where $\delta=|C_m-B_m|>0$. This step does not need
an unconditional bound on the first eigenvalue: that index remains in
the finite head.

If all head differences obey $|q_{n,j}-b_j|\le\varepsilon$, with
$\varepsilon\le b_1/2$, then $q_{n,j}\ge b_j/2$ because $b_j\ge b_1>0$.
Consequently
$$
|q_{n,j}^{-1}-b_j^{-1}|\le 2\varepsilon/b_1^2.
$$
Choosing $2J\varepsilon/b_1^2\le\delta/8$ makes the head error at most
$\delta/8$. Adding the two tails and the trace-limit error gives
$\delta\le\delta/2$, a contradiction. Thus some index in the same fixed
finite set has $|q_{n,j}-b_j|>\varepsilon$ for every sufficiently large $n$.

The constructed expansion polynomial $P_{n,j}$ satisfies
$P_{n,j}/h_n^s\to b_j$ without any assumption on the eigenvalue error,
by the implicit equation and Taylor's theorem. On a finite set this
convergence is uniform. Subtracting it proves
$$
\max_{1\le j\le J}|\lambda_{n,j}-P_{n,j}|
\ge(\varepsilon/2)h_n^{2m}
$$
for every sufficiently large $n$. The existing upper bound and bounded
$d_{2m}$ give the matching upper estimate for the full maximum.

This proves an eventual two-sided order-$h_n^{2m}$ maximum error.
It does not claim that the same individual index attains the lower
bound for every sufficiently large $n$, and the argument makes no such
unsupported selection.

## Scope

This cross-review checks the deductions from the stated trace limit,
bulk expansion, positivity, and interlacing. My separate bulk audit checks
the latter three mathematical inputs. The trace audit independently checks
the classical inverse-kernel source. Neither report converts the external
theorem or these deductions into an end-to-end Lean proof.
