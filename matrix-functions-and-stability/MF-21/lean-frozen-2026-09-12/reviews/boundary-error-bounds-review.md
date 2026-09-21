# Independent review: actual finite error expression bounds

Verdict: **APPROVE**, for the four printed results of
`MF21Restart/BoundaryErrorBounds.lean`. The source and mathematical review
is independent of its author. The reviewer did not compile Lean or edit
the reviewed source. This is a scoped ingredient review; the normalized
determinant identity and full MF-21 target are not proved by this module.

The unchanged manuscript `/private/tmp/mf21-solution.md` has SHA-256
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`.
The pinned referee standards have SHA-256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Exact source and statement

| File | SHA-256 |
| --- | --- |
| `MF21Restart/BoundaryErrorBounds.lean` | `b6b6d491b44d1992c1903fd6dcc82d726914f7d2b23866ae1b65f04d0370132e` |
| `BOUNDARY_ERROR_BOUNDS_STATEMENTS.md` | `51979e758ac233071a069c1618fb440f1fcf023816cad404cebddfd5dc3cb499` |
| `MF21Restart/NormalizedErrorCoefficient.lean` | `196098a5618651861b2d92ff8ce145b2e7425092241b97ed908a07b2bb85c52d` |
| `MF21Restart/NormalizedQuotient.lean` | `64b0c557994407c92cc1247d11d2701b2b3435acb966c9dabf95da9ddcb3863c` |
| `MF21Restart/BoundaryProductDecay.lean` | `f9f9b6b0d5c8b8842049f91850a3cb6d4482747443c1448d1c1e325bdcd0d0e3` |

The last three imported interfaces were inspected to determine whether
the public estimates hide assumed bounds. This reviewer authored an
earlier version of `BoundaryProductDecay`; this report does not claim a
new independent proof review of that dependency itself.

`BoundaryNonleadingSubset` at lines 12–15 contains exactly the actual
cardinality-m subsets other than the two specified leading sets. The
term at lines 17–20 is the actual constructed coefficient times the
actual product ratio to exponent `n+m`; the expression at lines 24–26
is the finite sum over those subsets. The two sets are removed by their
indices, so coincidence of root values at the endpoints does not change
the index family.

`boundaryErrorExpression_exp_bounds` at lines 104–110 has only `m ≥ 2`
as a mathematical premise. It chooses positive c and C before both n
and theta. It proves the exact value and derivative estimates
`C exp(-c n theta)` and `C (n+1) exp(-c n theta)` for every natural n
and every theta in `[0,pi]`. This matches the exponential factors and
normalization of manuscript (11), lines 122–132, for the finite expression
in (18), lines 202–208. Reality of that expression and its equality to
`D/N - sin F` remain explicitly separate, as required by the lock.

## Derivative and endpoint audit

The two regularity statements at lines 28–41 prove `ContDiffAt` in an
ordinary neighborhood at each point, including the endpoints. They do
not silently replace ordinary real differentiation by a derivative
within the interval. Their inputs are the constructed normalized
coefficient and product-ratio regularity, not new hypotheses.

`boundaryProductRatio_deriv_uniform_bound` at lines 45–65 obtains a
bound for each actual ratio derivative from compactness and then takes
one positive bound for the finite family. This uses no assumption of
bounded logarithmic derivatives. The finite sum plus one remains
positive even for an empty finite family; no unjustified nonemptiness
assumption is used.

The private power estimate at lines 67–80 has the correct monotonicity
direction: for `c ≥ 0`, `theta ≥ 0`, and `k ≥ n`,
`exp(-c theta)^k ≤ exp(-c n theta)`. At theta zero this simply gives the
valid bound one. It does not need strict contraction there.

The product derivative at lines 148–152 is proved from the genuine
`HasDerivAt.mul` and `HasDerivAt.pow` rules:
`a' b^(n+m) + a ((n+m) b^(n+m-1) b')`.
The exponents in both norm bounds are at least n (lines 139–142).
Thus the derivative retains the same exponential decay rate, including
when n is zero. This is a valid detailed implementation of the
manuscript's differentiation step at line 213; it does not introduce
an unproved reciprocal estimate or lose the decay by replacing
`b^(n+m-1)` with an unrelated bounded quantity.

The coefficient inequality at lines 153–160 uses
`n+m ≤ m(n+1)` and positivity of the actual derivative bound B. It yields
the required factor `n+1`, with all dependence on m absorbed in the
constant. The auxiliary scalar norm lemma uses the triangle inequality,
norm multiplicativity, `norm (k : Complex) = k`, and nonnegative factors;
its scalar premises are all discharged in the public proof.

The finite sum derivative at lines 187–191 is justified by the proved
differentiability of every term. Both sums are bounded symbolically by
the finite index cardinality, and `C = max (max V D) 1` is positive and
dominates both resulting constants. Nothing is enumerated numerically.
No constant depends on n or theta.

The imported normalized weights' exact equality with the denominator
displayed in (18) is not claimed here. The source therefore correctly
distinguishes a bound for the constructed expression from a completed
bound for the normalized determinant. No material mathematical,
statement-fidelity, or computational-scope issue was found.

## Actual local test evidence

The reviewer read `evidence/logs/boundary-error-bounds-01.json`, SHA-256
`740cfe9fdd3286b1ff08005594ef72877ec53ed75a7d27646862c15d1c4ddc02`.
It records the actual command
`lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/BoundaryErrorBounds.olean MF21Restart/BoundaryErrorBounds.lean`,
`LEAN_NUM_THREADS=1`, exit code zero, and unchanged source. The reviewer
independently recomputed and matched its source, log and output hashes.

The log has SHA-256
`8a7295e1f8fc5e36f28348038cb17f1c391d641a76f1142e00c8748bf3a016a6`.
All four printed results list only `propext`, `Classical.choice` and
`Quot.sound`. Its one unnecessary-sequence-focus warning is stylistic
and does not affect the proof. The output has SHA-256
`85984e9a232c23a9ef73d610143023a2c7f959282fd548ffc8496e47d940113d`.

No GitHub Comparator, Linux sandbox, final Target, or additional compiler
run is claimed by this review. The endpoint vanishing `E(pi)=0`, the
sharper endpoint estimate (12), and eigenvalue indexing are subsequent
obligations.
