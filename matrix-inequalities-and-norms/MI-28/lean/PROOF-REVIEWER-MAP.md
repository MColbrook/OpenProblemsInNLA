# MI-28 current proof map

This is the proof author's navigation map for the completed source. It is not
an independent review. Exact declarations, source/header hashes and locations
for C01–C20 are in [IMPLEMENTATION-MAP.json](IMPLEMENTATION-MAP.json); fresh
nonauthor review reports are indexed in [REVIEW-INDEX.md](REVIEW-INDEX.md).

For positive definite complex matrices, put

```math
M=|AB|,\quad H=A^{(p-k)/2}B^pA^{(p-k)/2},\quad
Z=A^{-k/2}M^pA^{-k/2}.
```

The frozen definitions use actual complex matrices, `CFC.rpow`, `CFC.abs`,
the norm of `Matrix.toEuclideanCLM`, and Mathlib's decreasing Hermitian
eigenvalue list with multiplicity. Every prefix length is represented,
including zero and the full dimension. The final statement has exactly
$`n\ge1`$, $`A,B>0`$, $`k\ge0`$, and $`0\le p\le2`$.

| Stage | Source and argument |
| --- | --- |
| C01–C03 | `Numerical`, `ModulusPowers`, `InverseSandwich`, `SwappedModulus`: kernel half certificate; concrete $`M^2=BA^2B`$; inverse congruence gives $`\lvert M^{-1}B\rvert=A^{-1}`$ with the exact factor order. |
| C04, C13 | `NormalizedPositivity`, `NormalizedHomogeneity`: genuine positive congruences and exact scaling of both normalized matrices by $`c^p`$. |
| C05–C06 | `FurutaBoundary`, `FurutaAdmissible`: extend the unchanged MI24 bounded Furuta proof. A known boundary at $`u`$ yields every $`r\in[u,1+2u]`$; induction on a natural upper bound covers all real $`r\ge0`$. One Loewner–Heinz step gives the admissible outer exponent. |
| C07–C08 | `FurutaSubstitution`, `LowerPowerImplication`, `HigherPowerOrder`, `HigherPowerImplication`: substitute $`X=A^k,Y=M^p,a=2/p,r=2/k`$. The low region uses $`q=2`$. The high region uses $`s=p(k+2)/(k+p),q=2/s`$, followed by proved negative-power order and a polar identity. All exponent conditions, including $`p=1,2`$, are proved symbolically. |
| C09–C10 | `SwapImplication`, `SmallBaseImplication`: apply the already-proved swapped implication to $`M^{-1},B`$, using C03. The $`p=k`$ exponent zero is allowed. A finite algebraic case split closes $`0<k\le2,0<p\le2`$ without a circular hypothesis. |
| C11–C12 | `NormalizedOrder`, `NormComparison`, `SmallBaseNorm`, `PositiveProductOrder`, `LargeBaseOrder`, `LargeBaseImplication`, `LargeBaseNorm`: scale $`B`$ by $`\|Z\|^{-1/p}`$, with $`\|Z\|>0`$. Congruence translates $`Z\le I`$ and $`H\le I`$ into the exact order implication. For $`k\ge2`$, the internally proved positive-product bound gives the large-base implication; no Ghabries/Cordes result is assumed. |
| C14 and endpoints | `NormalizedContinuity`, `FullNorm`: fixed unitary diagonalization reduces real-exponent continuity to positive scalar powers, reusing `Continuous.matrix_diagonal`. At $`p=0`$, $`H=Z`$. At $`k=0,p>0`$, use $`k_m=1/(m+1)`$ and closedness of order. This argument is applied to each compound norm. |
| C15 | `CompoundTransport`, `SpectrumDeterminant`, `NormalizedDeterminant`, `FullLogMajorization`: actual compound matrices preserve products, adjoints, positivity, all real powers and modulus. Their norms equal the products of the largest eigenvalues. Every degree $`j\le n`$ has positive compound dimension, including $`j=0`$, whose dimension and empty product are one. The full determinants agree independently, giving log-majorization rather than only weak log-majorization. |
| C16–C17 | `LogOneAddTangent`, `ProductOneAdd`: weighted AM–GM proves the logarithmic tangent inequality. Positive prefix products become prefix sums of log differences; the unchanged MI24 finite weighted-prefix lemma gives the product-of-one-plus comparison. All logarithm arguments are positive, and empty products are included. |
| C18–C20 | `DeterminantNormalization`, `DeterminantReality`, `DeterminantComparison`: factor the right sum using outer powers $`(k+p)/2,(k-p)/2`$, preserving $`A^pB^p`$ in order. Factor the left sum using $`k/2,k/2`$. Positive normalized determinants prove reality/positivity; multiply the scalar comparison by positive $`\det(A^k)`$. |

The large-base helper proves, for positive definite $`X,Y`$ and $`a,b\ge0`$,
that $`XY^aX\le Y^b`$ implies $`X^2\le Y^{b-a}`$. It treats $`a+b=0`$
separately and otherwise uses the positive congruence $`Y^{a/2}XY^{a/2}`$
and complementary power-order exponents. For $`D=BA^2B`$, this supplies the
necessary $`B^2\le D^{1-p/k}`$; the powers $`2/k,p/2,1-p/k`$ lie in their
required intervals. This is the internal proof replacing the canonical note's
cited large-base comparison, with prior mathematical credit preserved.

The 18 unchanged MI24 modules are the exact transitive closure needed by
`FurutaBase`, `PowerScaling`, `CompoundNorm` and `ScalarLogMajorization`, pinned
to publication revision `194c94929159b78758fd8b9d281f973c261dfabf` and the
authenticated local332 snapshot. The older combined `CompoundSpectral` module
imports `HeronNorm`, `HeronOrder` and `FurutaHalfPower`; these remain unchanged
dependencies. MI28 does not assume a Heron comparison as a substitute for its
own theorem. All previous code credits and the coordinator's authorship of the
scalar prefix argument remain intact in `REUSE-MI24-FURUTA.json` and source
headers. Shared Mathlib and LeanCert dependencies are not counted as new
problem proofs.

The local365 aggregate checks every selected declaration's permitted axioms
and kernel trust. Local366's actual body traversal confirms that the final
proof reaches C01 through C02 and the normalized determinant argument. See the
current numerical note for the exact generated certificates. These are actual
root compilation records, distinct from author/reviewer Python receipt checks.
No final Linux Comparator result is claimed.

The old implementation plan and numerical plan are archived under
`history/statement-draft/`. Draft-time comments in frozen `Definitions.lean`
and `Challenge.lean` remain literal historical bytes. No proof, frozen header
or mathematical definition is changed by publication documentation.
