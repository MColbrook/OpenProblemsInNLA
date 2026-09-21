# Dominated spectral trace passage (31)

Locked before the forthcoming SpectralTracePassage source, 20 September 2026.

Use zero-based counting index k and the actual term

```
f(m,n,k) = if k<n then (1/(n+2))^(2m)/eigenvalue(m,n,k+1) else 0.
```

Prove its exact tsum is (1/(n+2))^(2m) times the actual inverse trace,
using InverseSpectralTrace and finite support, with no missing first or last
index. For m>=1 and a=(m-1)/2, under the explicit fixed-index hypothesis

```
forall j>=1, (n+2)^(2m)*eigenvalue(m,n,j) -> pi^(2m)*(j+a)^(2m),
```

prove each f(m,n,k) tends to pi^(-2m)*(k+1+a)^(-2m). This is inversion
at a strictly positive limit, with k<n eventually.

The final passage takes the explicit additional majorant supplied by (22):

```
exists C>0,N, forall n>=N, 2<=j<=n:
  (1/(n+2))^(2m)/eigenvalue(m,n,j) <= C*(j^(2m))^(-1).
```

It proves the actual scaled inverse trace tends to
pi^(-2m)*sum_{k>=0}(k+1+a)^(-2m). The first term is bounded eventually by
its proved limit, rather than discarded or covered by an inapplicable j>=2
estimate. A convenient summable dominating function is

```
C*((k+1)^(2m))^(-1) + if k=0 then D else 0,
```

with D>0 obtained from first-term convergence. Summability comes from the
already proved even-zeta HasSum. Actual positive definiteness gives term
nonnegativity, so the norm bounds required by Tannery are legitimate.
Use Mathlib's proved tendsto_tsum_of_dominated_convergence (the counting-
measure dominated convergence theorem), including its eventual uniform
bound, and explicitly identify its finite sums with the actual trace.

These are conditional implications until the hypothetical global critical
bound supplies the fixed-index limit and actual interlacing supplies the
tail majorant. They must not be presented as an unconditional spectral
limit. The final contradiction uses the independently proved rational
trace limit (29), uniqueness of limits, and trace_series_irrational for
m>=3. No desired estimate or trace limit is an axiom.
