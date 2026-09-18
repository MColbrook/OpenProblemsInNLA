# MI-28 independent final source review

**Source verdict: PASS.** The reviewed Lean implementation proves the complete
unchanged canonical positive definite determinant target, including every
dimension `n ≥ 1`, arbitrary complex positive definite `A,B`, every real
`k ≥ 0`, and the closed real interval `0 ≤ p ≤ 2`. I found no mathematical or
statement-faithfulness blocker in the reviewed source. This verdict does not
claim completion of publication, Linux Comparator, a fresh independent Lean
run, external human peer review, or an official Tau Ceti engine run.

Reviewer: Codex agent `/root/mi28_final_referee1`, 18 September 2026. I did not
author or edit any of the reviewed mathematical statements or proof sources.
I have not written proof code during this review. The proof author and the
authors of the reused code are different agents, as disclosed in the source.

The immutable input is `MI28-local365-source-snapshot`, whose `MANIFEST.json`
has SHA-256
`7054f5dd7c6bfcd03916565315495d463ccd3fc39db72fad13d19f81d389c089`.
I read the canonical README and solution, all 20 challenge contracts, all 33
MI-28 component modules, `Solution.lean`, and all 18 reused MI-24 modules.
Thus the complete project proof import closure contains 52 modules. Shared
Mathlib and LeanCert dependencies are not counted as new problem proofs.
`READ-SCOPE.json` lists the exact source hashes and the additional material read.

## What the theorem actually says

`Mat n` is the literal matrix type `Matrix (Fin n) (Fin n) ℂ`.
`spectralPower` is Mathlib's `CFC.rpow`; `matrixModulus X` is `CFC.abs X`,
whose supplied primary library definition is `sqrt (star X * X)`.
`operatorNorm` is the norm of `Matrix.toEuclideanCLM X`. I inspected the
underlying library order definition `A ≤ B := (B - A).PosSemidef`, rather
than interpreting the matrix inequality as an entrywise comparison.

`normalizedH` is precisely
`A^((p-k)/2) B^p A^((p-k)/2)`, and `normalizedZ` is precisely
`A^(-k/2) |AB|^p A^(-k/2)`. The final `DeterminantComparison` quantifies
over the original parameters without extra spectral, commutation, norm,
Furuta, or conclusion assumptions. It asserts that both literal determinants
have zero imaginary part and that `determinantRight.re ≤ determinantLeft.re`.
This is the intended orientation of the original inequality. It does not
pretend the right matrix sum is Hermitian.

The stronger `FullLogMajorization` exports actual positive-definiteness
witnesses, all prefix-product inequalities, and equality of total products.
`sortedSpectrum` uses the decreasing Mathlib spectrum with multiplicities;
it is not an arbitrary enumeration or an entrywise diagonal. The original
canonical target concerns positive definite matrices. The informal note's
positive semidefinite extension is not silently added to the formal target.

## Complete mathematical audit

| Contracts | Independent check of the actual proof |
| --- | --- |
| C01–C03 | The half-exponent statement is exactly `0 < 1/2 ∧ 1/2 < 1`. Kernel-mode LeanCert supplies its proof. The lower bound is genuinely passed through `.1.le` to CFC composition in C02. The Gram product is `BA²B`; no factors are commuted. C03 inverts this positive congruence and cancels the adjacent powers of B to obtain the modulus of `|AB|⁻¹ B`, with that exact factor order, equal to `A⁻¹`. |
| C04 | Both normalized matrices are invertible Hermitian congruences of genuine positive CFC powers. This conclusion is proved for every real k and p. No positivity witness is assumed from the target. |
| C05–C06 | The reused Furuta base is proved from polar conjugation and power order. The new extension sends a known boundary at u to every r in `[u,1+2u]` using `t=(r-u)/(1+u)` and `s=(a+u)/(1+u)`. All denominators are positive. Induction on a natural upper bound covers every real r≥0; there is no hidden r≤1 or r≤2 restriction. C06 follows with outer power `(a+r)/((1+r)q) ∈ [0,1]`, and the exact exponent identities recover `1/q` and `(a+r)/q`. |
| C07 | The substitution `X=A^k`, `Y=|AB|^p`, `r=2/k`, `a=2/p`, `q=2` satisfies C06 precisely when `p≥k/(k+1)`. The actual inner sandwich is `(ABA)²`. Inverse congruence gives `B≤A^(k/p-1)`, and the admitted exponent p≤1 gives the desired conclusion. No restriction to integral parameters occurs. |
| C08 | With `s=p(k+2)/(k+p)` the proof checks s>0, s≤2, q=2/s≥1, and exact Furuta admissibility. From `C^s≤A^(k+2)`, C=ABA, the internally proved negative-power order gives `A⁻²≤C^(-2p/(k+p))`. The actual invertible factor `S=A⁻¹C^(1/2)` has `SS*=B`; its polar identity and the powers p−1 and `(k-p+2)/(k+2)` in `[0,1]` give `B^p≤A^(k-p)`. The endpoints p=1 and p=2 are both admitted. No negative-Furuta oracle is used. |
| C09–C10 | The universally quantified swapped implication is applied to `(A',B)=(|AB|⁻¹,B)` only after C03 has proved the required modulus. Powers p/k and `(k-p)/k` are in `[0,1]`, including zero at p=k. The small-base partition closes below `p=k/(k+1)` by invoking already proved lower- or higher-power results at the swapped parameters. It is not circular. |
| C11–C13 | The positive definite Z has strictly positive Euclidean operator norm in positive dimension. Scaling B by `c^(-1/p)` genuinely scales both H and Z by c⁻¹; all scalar bases are positive. The congruence equivalences exactly translate Z≤I and H≤I to the order implication. For k≥2 the independent `PositiveProductOrder` argument proves the published large-base range internally: `XY^aX≤Y^b` with a,b≥0 implies `X²≤Y^(b-a)`, using the positive congruence C and complementary powers. The a+b=0 case is handled separately. With D=BA²B, powers 2/k, p/2, and 1−p/k are all admitted. No cited inequality is inserted as a premise. |
| C14 | One fixed unitary diagonalization of A and continuity of positive scalar powers give continuity in k on all of ℝ. The norm is explicitly the L2/Euclidean operator norm. No continuity of a chosen ordered eigenbasis is assumed. |
| C15 | The complete norm proof handles p=0 by literal equality of H and Z, then handles k=0, p>0 by the sequence `1/(m+1)` and closedness of real order. These norm inequalities are applied to every actual complex compound matrix. The imported compound theory uses literal minors, proves product/adjoint/all-real-power covariance, and proves the norm equals the descending prefix product. For j=0 the compound dimension is one and the product is empty (=1); for every j≤n its dimension is positive. The full determinant identity is proved separately from C02 and positive determinants, so total products agree exactly, not only by an inequality. |
| C16–C17 | Weighted AM–GM with weights `1/(1+a)` and `a/(1+a)` and positive data `1,b/a` proves the exact tangent inequality. Every logarithm has a proved positive argument. Prefix-product domination becomes nonpositive prefix sums of log differences. The nonnegative weights a/(1+a) are antitone because a is antitone. The reused finite summation-by-parts lemma then gives the product-of-one-plus inequality. Sorting b is unnecessary, consistently with C17. Empty vectors also cause no failure. |
| C18–C20 | The right factorization has outer exponents `(k+p)/2` and `(k-p)/2`; multiplying out gives exactly `A^k+A^pB^p` in that order. The left factorization uses outer exponents k/2 and gives exactly `A^k+|AB|^p`. Determinants multiply through the factorizations. Their middle positive definite matrices prove both determinant reality and strict positivity. The final comparison multiplies `det(I+H)≤det(I+Z)` by the positive `det(A^k)`, yielding the correct original orientation. |

The deliberately general helper assumptions, such as a known order comparison
in the Furuta step or a universal swapped implication, are all discharged on
the final route. They are not extra assumptions on the original target.

## Local execution evidence inspected, not rerun

I executed the adjacent Python byte-verifier, not Lean, Lake, Comparator,
lean4export, a kernel replay, or a Tau Ceti review engine. It authenticated:

* all 83 files named by the frozen snapshot manifest;
* all 52 project proof-source hashes and the complete import closure from
  Solution, with no import of the intentionally sorried Challenge;
* the 20 frozen textual headers and the three frozen statement/config files;
* all 18 unchanged MI-24 copies against the retained original snapshots;
* all 52 successful source-bound compiler commands, originating in 18 retained
  local receipts, their logs and current matching compiled-output hashes;
* 92 retained execution-evidence files, the exact local365 assembly, and
  the recorded one-process, one-thread, 4096 MiB configuration;
* all 20 actual separate-environment type/universe comparisons from local366,
  whose source code erases binder names only;
* all six reported paths in the actual elaborated-body dependency graph.

The local365 aggregate log reports exactly the permitted standard axioms
`propext`, `Classical.choice`, and `Quot.sound` for all 20 selected contracts.
I read that actual log and the actual diagnostic source. The final theorem's
body reaches C01 through the proved modulus/determinant route and reaches the
two generated closed LeanCert strict-bound certificate constants. The source
shows the lower-half domain witness being used in C02; the upper-half bound
is co-certified in C01, and I do not claim it is independently necessary to
the mathematics. No matrix-entry interval grids or sampled parameter checks
replace the universal proof.

The mixed local365 batch also contains unrelated MF-14 failures; those are
explicitly retained in the source-completion record. They are not recast as
MI-28 successes. Exact local366 comparison record SHA-256:
`54cbbfe2497939fe78fbff9dd499b99c961316f6a22e36a98ba0fa7cc0256d45`.
These file and receipt checks establish internal provenance consistency. They
are not a fresh execution of the Lean checker or independent cryptographic
attestation of the coordinator's original invocation.

## Tau Ceti rubrics applied within this project's scope

I read the supplied pinned `REVIEWING.md` and correctness, generality,
proof-quality, attribution, and reuse rubrics. This is a nonauthor source
review applying those rubrics, not an official Tau Ceti scoreboard.

* **Correctness/faithfulness: approve.** I explicitly tested the meanings of
  powers, modulus, order, norm, sorted eigenvalues, determinant reality, endpoint
  limits, and discharged helper premises. The target was not replaced by a
  tautology or made vacuous by an impossible structure assumption.
* **Generality: approve for the problem project.** The final theorem has the
  entire required scope, and its reusable internal lemmas often have wider
  scope. Some frozen helper signatures retain hypotheses not needed by their
  proof (for example hA in homogeneity). This is harmless specialization of a
  fixed problem contract, not narrowing the final target. I am not requiring
  a redesign into a Mathlib contribution as a condition of this review.
* **Proof quality: approve for this source.** The long mathematical arguments
  are separated into meaningful intermediate modules and named lemmas; their
  noncommuting algebra and parameter transformations have explanatory comments.
  The `change`/`show` bridges at matrix/CFC namespace boundaries are explained.
  No native-decide shortcut, new axiom, sorry, admit, unsafe declaration, or
  custom elaborator appears in the project proof closure. The challenge alone
  intentionally contains statement placeholders.
* **Attribution: approve for source.** George Stepaniants and his Department of
  Computing and Mathematical Sciences, California Institute of Technology,
  affiliation are present. Prior mathematical credit to Ghabries, Abbas,
  Mourad, Assi, Furuta/Fujii, and the canonical solution is retained. The 18
  reused MI-24 files retain their original code credits; ScalarLogMajorization
  retains its coordinator authorship. Numerical and adapted matrix proof
  patterns have explicit provenance. No email is needed or included in the
  proof credit.
* **Reuse: approve within the bounded search scope.** Exact searches of all
  new declaration names and targeted mathematical searches in the supplied
  local Mathlib found no replacement for the full Furuta extension, parameter
  swap, normalized comparison, or determinant theorem. Relevant CFC, inverse,
  determinant, spectral, continuity, weighted-AM–GM and finite-product APIs
  are actually reused. Existing MI-24 theory is vendored unchanged with its
  provenance; the three small private norm bridges specialize the frozen
  MI-28 wrapper and have real consumers. `CFC.abs_mul_abs` offers a shorter
  route to a related modulus identity, but this project's chosen CFC
  half-composition route deliberately consumes the required frozen LeanCert
  certificate. I do not classify that as an uncredited duplicate library API.
  The full TauCeti theorem corpus was not supplied or searched. Search commands
  and outputs are retained; this is not a claim of an exhaustive worldwide
  prior-formalization search.

I also read the supplied Forsythe and Schiffer challenge examples, the Forsythe
numerical-target note, the MF05 numerical pattern, Comparator's README, and
the formalization.yaml README. They support the separate trusted statement
module, minimized genuine numerical certificate, and explicit provenance
layout used here. The pinned schema is byte-authenticated, but this source
snapshot contains no final formalization.yaml to assess or validate.

## Publication requirements outside this proof verdict

The supplied snapshot is a source checkpoint, not the publication package.
Before publication, current documentation must clearly identify the stale
"UNELABORATED/no Solution" source comments and the old unimplemented plan
statements as historical pre-implementation records. Preserve the frozen
mathematical bytes and state current status in the publication README and
proof map. The current lakefile defaults to Challenge; the published default
build should select Solution, and the lockfile's stale NLAMI22 top-level name
should be reconciled with NLAMI28 without changing dependency pins.

The final package still needs its truthful co-located formalization.yaml,
publication documentation review, and the separate genuine non-root Linux
Comparator/default-kernel/sandbox/negative-control checks. Those checks must
be tied to the actual published source/commit. None is marked as run by this
review. No campaign count changes, status edits, Git operations, network
requests, pushes, or PR actions were performed by this reviewer.
