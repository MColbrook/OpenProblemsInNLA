# Independent review of the final trace and uniqueness assembly

Date: 20 September 2026. Reviewer: Codex subagent `/root/trace_audit`.

## Scope and independence

I reviewed the root agent's [ActualTraceObstruction.lean](lean-development-source.tar.gz) and [ToeplitzTraceLimit.lean](lean-development-source.tar.gz), and the Lean agent's [CoefficientUniqueness.lean](lean-development-source.tar.gz), [LogSquaredMesh.lean](lean-development-source.tar.gz), [MF21CoefficientUniqueness.lean](lean-development-source.tar.gz), [QuantizationTaylor.lean](lean-development-source.tar.gz), and [Challenge.lean](lean-development-source.tar.gz). This is an independent review of those agents' assembly and statement choices, not external human peer review.

I authored several inputs used by the assembly: the generic finite-head trace obstruction, spectral trace identity and bounds, exact shifted-series arithmetic, and the pi-transcendence integration. I therefore do **not** characterize this as an independent audit of those inputs. Their separate mathematical checks and kernel checks remain relevant; a second reader must assess their informal interpretation independently. The present review checks how the independently authored assembly specializes these inputs and whether the resulting claim is the intended one.

**Verdict:** I found no mathematical or quantifier gap in the reviewed trace obstruction or coefficient-uniqueness assembly. The argument proves an eventual lower bound on a fixed finite head, not merely an upper estimate or a subsequence statement. The final target proposition has the intended matrix, mesh, cutoff, common-family quantifier, and orders. The final all-m theorem assembly is reviewed in the addendum below.

## Trace obstruction

`scaledEigenvalue m n j` equals `(n+2)^(2m) λ_(n,j+1)` whenever `j<n`. Zero padding outside that range only supports fixed-index notation and disappears before conversion to a `Fin n` index. The profile is exactly

```math
b_{j+1}=\bigl((j+1)\pi+(m-1)\pi/2\bigr)^{2m}.
```

There is no shift from `n+2` to `n+1`, and no shift in the first source index. `profile_inverse_sum` identifies the reciprocal-profile sum with the actual infinite series in `MF21Audit.modelTrace`; it is not an unconstrained constant.

`actual_finite_head_separation` supplies every hypothesis of the generic trace lemma using the actual ordered Toeplitz eigenvalues. Positivity is actual matrix positivity. The inverse tail bound is the proved circulant/interlacing estimate, with a summable `m^(2m)/(j+1)^(2m)` majorant for zero-based `j≥1`. This is slightly weaker in its constant than the manuscript's bound, but fully sufficient. The first source index is intentionally excluded from the uniform tail majorant and included in the finite head; no uncontrolled first term is discarded.

The actual normalized trace limit is the rational factorial expression derived by `ToeplitzTraceLimit` from exact finite inverse columns and trace increments. Its normalization agrees with `(n+2)^(-2m)`. The distinct model sum is established independently from the exact shifted-zeta formulas and transcendence of pi. Only inequality of the two constants is used; their relative order is never assumed.

The finite-head conclusion is strong:

```math
\exists J\ge1\;\exists\varepsilon>0\;\forall\text{ sufficiently large }n,
\quad n\ge J\quad\text{and}\quad
\exists j<J:\ |(n+2)^{2m}\lambda_{n,j+1}-b_{j+1}|>\varepsilon.
```

The index may vary with `n`, which is exactly what the maximum-error conclusion needs. It need not be one fixed offending eigenvalue for every large matrix.

`approximation_profile` specializes `Model.coefficient_fixed_index_profile` with `c=(j+1)π` and `h=(n+2)^(-1)`. It proves the truncated coefficient model divided by `h^(2m)` tends to `b_(j+1)` for each fixed index, using only the actual smooth implicit model and uniform Taylor theorem. It does not assume an eigenvalue expansion at that index. Eventual strip membership is proved from positive `c`, positive `H`, and `h→0`.

`model_finite_head_lower_bound` then transfers separation from the profile to the finite Taylor sum, losing only a factor two. `model_finite_head_remainder` converts the padded index back to the source grid and the exact `Challenge.remainder`. Its strict lower bound is stronger than the non-strict lower bound stated in manuscript Corollary 6. `model_not_uniform` combines that lower bound with a putative `D h^(2m+1)` upper bound and chooses `n+2>D/ε`; this is the required contradiction. Thus the argument explicitly resolves the upper-bound objection to equation (25).

## Uniqueness and arbitrary alternative families

`top_expansion_unique_on_mesh` requires only the top-order difference estimate. It does not quietly assume estimates for every lower truncation. Its induction eliminates all lower coefficients exactly on the domain. Higher coefficients remain bounded along the convergent mesh by continuity, so every higher power is little-o of the current power. The nonzero mesh scale permits division. Continuity is `ContinuousOn`, not ambient continuity.

`LogSquaredMesh.index` clips the floor approximation between the cutoff and `n`, also enforcing index at least one. The mesh stays in `[0,π]`, becomes admissible, and converges to every point of the closed interval, including both endpoints. The proof of endpoint equality therefore does not assume an extension of the coefficients beyond the interval. The log-squared cutoff-to-dimension ratio tending to zero is actually proved.

`MF21CoefficientUniqueness` converts one-based natural source indices to `Fin n` with `j-1` and proves `j-1+1=j` under the admissibility condition. It preserves the exact grid and cutoff. `mf21_uniform_coefficients_eq_bulk` therefore identifies any hypothetical continuous global order-`2m` family with the constructed bulk family on the complete coefficient domain. `uniformOrder_congr` transfers the hypothetical bound back to the constructed family at every actual grid point. This addresses the separate uniqueness objection without imposing extra smoothness on the hypothetical family.

`universalObstruction_of_fullTarget` is correctly an implication from the same-family original target to the stronger no-continuous-family assertion. It does not substitute the stronger assertion for the original problem or assume that implication's antecedent has already been proved merely because a proposition definition exists.

## Canonical target correspondence

The retained [canonical statement](../../matrix-functions-and-stability/MF-21/README.md) and `Challenge.TargetAt` agree on all quantifiers:

- The parameter is every natural `m≥3`.
- One real coefficient family is chosen for each `m`, before any `n,j,p` estimates; it is independent of matrix dimension and eigenvalue index.
- Continuity and `d_0=g_m` hold on the entire closed interval.
- The sum includes every coefficient from zero through `p`.
- Every natural `p≤2m−1` has a positive uniform constant and eventual dimension threshold, independent of `n,j`.
- Top order uses precisely `ceil(log(n+2)^2)≤j_source≤n` and remainder exponent `2m+1`.
- Failure of global top order is asserted for the **same** family.

The natural `m` and `p` encodings introduce no restriction under the stated integer/nonnegative assumptions. Truncated natural subtraction at `2m-1` is harmless because `m≥3`. Including matrix size zero in the ambient quantifier is harmless because `Fin 0` is empty and thresholds can be enlarged. Coefficients indexed beyond `2m` and their values outside `[0,π]` are unused.

The matrix uses exact signed-binomial Toeplitz entries, without wraparound. The actual library Hermitian eigenvalues are reversed because `eigenvalues₀` is antitone, so the resulting order is increasing with multiplicity. Source index equals `Fin.val+1`.

Unlike the earlier 19 September statement-only review, the Fourier bridge is now present: `MF21Fourier.sourceCoefficient_eq` identifies the explicit entries with the original complex Fourier integral, and `toeplitz_eq_source` identifies every Toeplitz entry. The integral normalization is `1/(2π)`, interval `[-π,π]`, and exponential `exp(-iqθ)`, exactly as in the source. The zero-based matrix-index conversion preserves index differences. The earlier review's statement that this bridge was unproved is therefore a historical status, superseded by this review.

## Kernel checks performed for this review

I reran the current source files `ActualTraceObstruction.lean`, `CoefficientUniqueness.lean`, `LogSquaredMesh.lean`, and `MF21CoefficientUniqueness.lean` with Lean 4.33.1 and `--trust=0` using the pinned mathlib build. Every printed capstone reported only `propext`, `Classical.choice`, and `Quot.sound`. These targeted checks are separate from the clean full source replay assigned to another agent; they do not replace it.


## Final capstone addendum

After the author froze [FinalTarget.lean](lean-development-source.tar.gz), I independently inspected its final definitions and assembly and reran it with `--trust=0`. All eight printed exports passed with exactly `propext`, `Classical.choice`, and `Quot.sound`.

`MF21Verified.targetAt` chooses `actualModel m` once. Its `model.d` is the identical family supplied to continuity, leading-coefficient equality, every lower-order uniform bound, the bulk top-order estimate, and the trace obstruction. The actual tail-angle theorem discharges the previously conditional expansion-transfer input. The choice of model is justified by the proved `model_exists`; neither existence nor an eigenvalue asymptotic is postulated.

`MF21Verified.fullTarget : MF21Challenge.FullTarget` has no hypotheses. It supplies the complete original all-`m≥3` target. `universalObstruction` also has no hypotheses and follows by the independently reviewed uniqueness implication. There is no hidden restriction to selected values of `m`, to an arbitrary substitute spectrum, to a nonuniform index range, or to a subsequence of matrix sizes.

The additional `smooth_common_family` export chooses the same family for the complete target, smoothness, the eventual finite-head lower bound, and the global `h^(2m)` upper bound. These latter bounds imply the manuscript's maximum-error statement: a maximum over all indices is at least the witnessed finite-head error and is bounded above by the all-index estimate. Its lower-bound index can vary with matrix size, just as in Corollary 6. `fourier_matrix_entries` explicitly displays the source integral, so the matrix-definition bridge is visible at the capstone boundary.

I found no remaining semantic or quantifier gap in this final source. This conclusion concerns the reviewed source snapshot and the targeted kernel checks. The separate fresh full dependency replay and the later canonical package/import migration require their own verification; neither is certified merely by this addendum.

### Reviewed source hashes

SHA-256 values at completion of this review:

| Source | SHA-256 |
| --- | --- |
| `Challenge.lean` | `0c18548156a323e2554d97a1f99739bbf8abb7a52b4e821669f0e7bf1217c302` |
| `ActualTraceObstruction.lean` | `30cbfbd2af2d1fdeab80a12783105bdde2e81e7ca859fcc3a9cbfb6a49eced0e` |
| `ToeplitzTraceLimit.lean` | `9a8e9830dfa6201d7a1e13153179f95fc5061a71ab483c115e62b4d1aa6e4410` |
| `CoefficientUniqueness.lean` | `9a32b2f97a400e86fd934d5ff18d94e2c8d46fa746d6c33dc571ced519a7de56` |
| `LogSquaredMesh.lean` | `faeca4b2e92aa3c88f741e7ddb3b40dbbca70353b6587e760b3ede33a33c5635` |
| `MF21CoefficientUniqueness.lean` | `bb52497b59a734dc526f5a2fa790e5dd47bb69146ffd9f0b6efb86cc6cec6005` |
| `QuantizationTaylor.lean` | `9b660a7eb8ba3eaa0107b9e49bb2baabf70e8539ed20dc52f15b41b1c190fc79` |
| `FourierCoefficients.lean` | `56df75748a30449cbf4e1c7e173e54bfbbd9faef1e88f83667327b17263b1b39` |
| `FinalTarget.lean` | `065c08e12c733e8b933773292670b4beedbaf76a19c18579a12e353e9823bffd` |
