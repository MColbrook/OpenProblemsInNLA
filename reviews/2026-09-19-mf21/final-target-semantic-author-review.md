# MF-21 final target correspondence check

Date: 20 September 2026. Reviewer: Codex AI agent `/root/lean_audit`.

**Authorship limitation:** this agent authored the original `Challenge.lean`, the uniqueness and quantization/expansion modules, and `FinalTarget.lean`. This is an author correspondence check, not an independent referee report. It must not count toward the repository's two independent final reviews. The independent agents' statement and final reviews are separate artifacts.

**Verdict:** no target mismatch found. The unchanged mathematical `Challenge` definitions faithfully encode the retained problem, and the final exports prove that target plus the explicitly stronger conclusions below. The Fourier correspondence is now proved, rather than assumed.

## Frozen files inspected

| File | SHA-256 |
| --- | --- |
| `lean/Challenge.lean` | `0c18548156a323e2554d97a1f99739bbf8abb7a52b4e821669f0e7bf1217c302` |
| `lean/FinalTarget.lean` | `065c08e12c733e8b933773292670b4beedbaf76a19c18579a12e353e9823bffd` |
| `lean/FourierCoefficients.lean` | `56df75748a30449cbf4e1c7e173e54bfbbd9faef1e88f83667327b17263b1b39` |
| canonical `MF-21/README.md` at this inspection | `1c17249b14c5288ab15506b90312515ea06da36cff80cebf2acf1dc2a1138ab6` |

I reread the canonical statement, the revised manuscript's Theorem 1 and Corollary 6, and [Conjecture 8.4 on printed page 26 of the original preprint](https://arxiv.org/pdf/1710.05243). The conjecture uses the `n+2` grid, all lower orders through `2m-1`, the failure at order `2m`, and a logarithm-squared restriction for its surviving bulk estimate. Continuity and uniqueness are the source's regular-expansion convention, explained in Theorem 1.2 and Remark 8.3. Rounding the cutoff upward exactly translates its inequality to integer source indices.

The changes since the two earlier independent Challenge reviews are comments reporting completion of the Fourier bridge. A direct diff against the prior file shows no change to any mathematical definition or theorem type.

## Actual definitions checked

- The field is real for the matrix and its ordered spectrum. `coefficient m d` is `(-1)^d * choose(2m,m+d)`. For `d>m` the binomial coefficient vanishes; there is no natural-subtraction truncation or periodic wraparound. `Nat.dist` is the absolute difference of matrix indices.
- `fourier_matrix_entries` exports the actual integral identity, including factor `1/(2*pi)`, interval `[-pi,pi]`, and exponent `-i*(i-j)*theta`. It quantifies over every `m,n` and every matrix entry. Zero-based matrix indices preserve source differences exactly.
- I inspected `Mathlib/Analysis/Matrix/Spectrum.lean` at pinned commit `0df444a360eaa60ab8c11dca51a86af692955474`. `eigenvalues₀_antitone` gives descending order; `roots_charpoly_eq_eigenvalues₀` gives the actual multiset of characteristic roots. `Fin.rev` reverses that order, and the cardinality cast does not change an index. Thus `j : Fin n` represents source index `j.val+1`, including multiplicities.
- The symbol is exactly `(2*sin(theta/2))^(2m)`. `grid n j` is exactly `(j.val+1)*pi/(n+2)`. The remainder sums all orders `0,...,p`, including both endpoints. All divisions use `n+2`, not `n`, `n+1`, or an asymptotically equivalent substitute.
- `FullTarget` is `forall m : Nat, 3 <= m -> TargetAt m`. Each `TargetAt` first chooses one coefficient family, then states every estimate for that same family. Coefficients cannot depend on dimension or spectral index.
- Positive constants and natural thresholds precede the universal dimension and index quantifiers. They may depend on `m` and truncation order. The lower-order quantifier covers every natural `p <= 2m-1`, including zero. Natural subtraction is harmless because `m>=3`.
- `ContinuousCoefficients` requires continuity on the entire closed interval `[0,pi]`, including both endpoints. Defining the functions on all reals does not constrain their values outside this interval. The leading coefficient agrees with the symbol on the whole closed interval.
- `BulkTopOrder` uses the exact natural ceiling of the square of the natural logarithm and source indices `j.val+1`. Its remainder exponent is `2m+1`. `TargetAt` negates the corresponding all-index uniform assertion for the same family. Dimension zero is vacuous because `Fin 0` is empty and causes no weakening of the eventual statements.

## Final exported scope

`MF21Verified.fullTarget` has no assumptions. `targetAt` has only the source assumptions `m : Nat` and `3 <= m`. In particular, no phase-root, determinant, eigenvalue asymptotic, coefficient-existence, Fourier-bridge, trace-limit, or mesh-density assumption remains.

`universalObstruction` separately rules out every continuous coefficient family. Its stronger quantifier is not substituted for the source's same-family assertion; the proof uses actual bulk existence and the closed-interval coefficient uniqueness theorem.

`smooth_common_family` chooses one family satisfying all original assertions, requires smoothness through every coefficient order used by the target, and proves both an eventual positive lower bound on one fixed finite head and a uniform upper bound on all indices at scale `(n+2)^(-2m)`. The index witnessing the lower bound may vary with dimension, exactly as a maximum-over-a-finite-head assertion permits. The theorem makes no unsupported claim about a single fixed index attaining that bound for every dimension.

## Mechanical and review boundaries

All eight capstones in `FinalTarget.lean` passed local Lean 4.33.1 `--trust=0`; every printed transitive axiom closure contains only `propext`, `Classical.choice`, and `Quot.sound`. The source and output hashes are in `lean/verification/final-target-raw-result.json`.

I reread `CONTRIBUTING.md` sections on Lean verification and `docs/lean/README.md` and `REVIEW.md`. Local macOS raw-kernel acceptance is distinct from a fresh full-project replay, independent final source reviews, and the pinned non-root Linux sandboxed Comparator run with rejection controls. This report does not claim those separate gates were completed and does not authorize a status promotion or push.
