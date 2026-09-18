# MI-28 independent final source review, referee 2

Reviewer: Codex agent `/root/mi28_final_referee2`, 18 September 2026.

**Mathematical and proof-source verdict: APPROVE.** I found no missing hypothesis,
weakened target, unproved mathematical premise, endpoint omission, or incorrect
noncommuting factor manipulation in the reviewed candidate. This approval covers
the unchanged canonical positive-definite target and all 20 frozen contracts.
It is not a claim that Comparator has run, that the package has been published,
or that this review constitutes external human peer review.

**Publication disposition: two build/package corrections and clear historical
status labeling are required before release.** These do not invalidate the
mathematical source approval; they require a separate checked packaging update.

## Independence and exact scope

I did not author or edit any candidate proof, definition, contract, or reused
module. I did not consult the other final referee's verdict or report. I did not
run Lean, Lake, Comparator, Git, a network command, or a publication operation.
My writes are confined to this review directory. I reviewed the original
canonical README and analytic solution supplied in the packet, rather than
treating successful compilation as evidence of faithful formalization.

The reviewed immutable snapshot is
`MI28-local365-source-snapshot/MANIFEST.json`, SHA-256
`7054f5dd7c6bfcd03916565315495d463ccd3fc39db72fad13d19f81d389c089`.
I read the complete text of every one of its 52 proof-side Lean source files:
33 `NLA/MI28` modules, 18 unchanged `NLA/MI24` modules, and `Solution.lean`.
I also read the complete `Challenge.lean`, definitions, numerical and
implementation plans, selected-header inventory, Comparator configuration,
dependency files, reuse record, and relevant verification records. The source
inventory accompanying this report identifies all exact proof-source hashes.
The challenge has 20 intentional `sorry` bodies; it is not imported anywhere
in the solution's import closure.

I read the retained Tau Ceti `REVIEWING.md` and correctness, generality,
proof-quality, reuse, and attribution rubrics. I applied their semantic and
quality criteria manually within this standalone verification project's scope.
I did not execute the Tau Ceti review engine or claim its clean-room isolation.
I also read the retained Comparator and formalization.yaml README files. A
final `formalization.yaml` and Linux execution evidence are not part of this
source checkpoint and remain separate publication gates.

## Faithfulness of the target and definitions

The original target quantifies over every integer dimension `n >= 1`, complex
positive-definite matrices `A,B`, real `k >= 0`, and real `0 <= p <= 2`, and
compares `det(A^k + |AB|^p)` with `det(A^k + A^p B^p)`. The frozen
`DeterminantComparison` has exactly these quantifiers and the correct inequality
direction. It additionally makes both imaginary parts zero, correctly giving
the real-order meaning of the complex determinants. No commutativity, matrix
entry bound, spectral gap, upper bound on `k`, or imported desired inequality
has been inserted as a premise.

`Mat n` is the actual complex square matrix type. `spectralPower` is
`CFC.rpow`; `matrixModulus` is `CFC.abs`, whose pinned Mathlib definition is
`sqrt (star a * a)`, rather than entrywise absolute value. `operatorNorm` is the
norm of `Matrix.toEuclideanCLM`, explicitly reconciled with the scoped L2
matrix norm. `sortedSpectrum` is Mathlib's decreasing Hermitian eigenvalue list
with multiplicity; the finite index casts do not permute away the decreasing
order. `prefixProduct` ranges over every initial segment, including length
zero and the whole dimension. `LogMajorized` includes equality of the full
products. Positive-definiteness witnesses in `FullLogMajorization` are produced,
not assumed in lieu of proving positivity.

`OrderImplication` is a universally quantified intermediate assertion, not an
axiom. Its premise is discharged in every final application. The explicit
conditional contract C09 is used only after the swapped implication has been
proved from C07/C08. The final C20 has no such conditional premise.

## Audit of all 20 contracts

| Contracts | Source and semantic checks |
| --- | --- |
| C01 | Kernel-mode `interval_decide` proves exactly `0 < 1/2` and `1/2 < 1`. There is no matrix or real-parameter sampling. The certified nonnegative half supplies an actual CFC power-composition hypothesis in C02. |
| C02 | `(AB)* (AB) = B A^2 B` uses Hermitian factors in the correct order. Composing the nonnegative half power with power two recovers the Gram matrix. |
| C03 | With `M=|AB|`, the proof computes `M^-2=B^-1 A^-2 B^-1`, cancels in `B M^-2 B`, and identifies the positive square root of the new modulus square. It uses `M^-1 B`, not the reversed product. |
| C04 | Both normalized matrices are genuine positive-definite congruences. Invertibility of `AB` supplies positivity of its modulus. All real exponents in this auxiliary contract are covered. |
| C05 | The imported Furuta base has sandwich parameter in `[0,1]`; the new proof really extends it. A boundary at `u` reaches `[u,1+2u]`, and induction on a natural upper bound covers every real `r >= 0`. The Archimedean step imposes no finite cutoff. All reciprocal denominators are strictly positive. |
| C06 | A single Loewner-Heinz exponent `(a+r)/((1+r)q)` lies in `[0,1]` by the stated admissibility inequality and gives exactly outer power `1/q`. |
| C07 | Substitution `X=A^k`, `Y=|AB|^p`, `a=2/p`, `r=2/k`, `q=2` has its admissibility algebra proved. The concrete square is `(ABA)^2`; inverse congruence and the admissible power `p` produce `B^p <= A^(k-p)`. |
| C08 | The choice `s=p(k+2)/(k+p)`, `q=2/s` is admissible for every `k>0`, `1<=p<=2`. The subsequent negative-power order, polar identity for `S=A^-1 C^(1/2)`, and two Loewner-Heinz steps retain both closed endpoints. No negative-Furuta theorem is assumed. |
| C09 | Inversion and C03 supply the premise for `(M^-1,B)` at the swapped parameters. The exponents `p/k` and `(k-p)/k` are in `[0,1]`. The latter is allowed to be zero when `k=p`. |
| C10 | The branch split `p>=1`, then `p>=k/(k+1)`, then the swapped lower/higher cases covers the full stated small-base rectangle. The fallback has `p<k`; no circular appeal to C10 occurs. |
| C11 | The shared norm argument scales `B` by `c^(-1/p)`, where `c=||Z||>0`; positivity uses the genuine nonzero dimension. The exact homogeneity factor is `c^-1`. The normalized order implication is discharged by C10. |
| C12 | The formerly cited large-base result is proved internally. From `D^(p/2)<=A^k`, `D=B A^2 B`, power `2/k` and positive-product contraction give `B^2<=D^(1-p/k)`. The final powers `p/2` and `1-p/k` are in `[0,1]`. The contraction lemma handles its zero denominator case separately. C02 identifies the actual modulus, and the same norm argument applies. |
| C13 | Both normalized matrices scale by the exact positive real power `c^p`. Modulus homogeneity is for the actual product and norm of a positive real scalar. The real/complex scalar bridge is explicit. |
| C14 | A fixed positive matrix has a fixed unitary spectral decomposition, and its strictly positive scalar eigenvalues have powers continuous in the exponent. Continuity of the two actual normalized norms follows without an assumed eigenvalue-continuity theorem. |
| C15 | The all-parameter norm theorem applies to each actual compound matrix. Compounds preserve ordered multiplication, adjoints, positivity, modulus and all real powers. Their Euclidean norm equals the product of the largest eigenvalues by an explicit finite-subset argument. Determinants of the two normalized matrices agree, providing the full-product equality. |
| C16 | Weighted AM-GM with weights `1/(1+a)` and `a/(1+a)` and entries `1,b/a`, followed by logarithms of strictly positive quantities, has the correct tangent-inequality direction. |
| C17 | Prefix-product inequalities become nonpositive prefix sums of logarithmic differences. The weights `a/(1+a)` are nonnegative and decreasing with the descending `a`. The proved finite summation-by-parts lemma yields the claimed product inequality. Sorting `b` is not needed. Empty sequences are included. |
| C18 | The right sum is factored with outer factors `A^((k+p)/2)` and `A^((k-p)/2)`, so the middle `I+H` produces exactly `A^k + A^p B^p` in that order. Only under the determinant are the outer factors combined. The left sum uses the genuine `A^(k/2)` congruence. |
| C19 | Positive-definite `A^k`, `I+H` and `I+Z` have positive real complex determinants; the factorizations give reality and positivity of both original determinants. No Hermitian claim is made about the right-hand matrix. |
| C20 | C15, C17 and the positive determinant factor give the original inequality. C19 supplies both imaginary-part equalities. No auxiliary inequality remains as a hypothesis. |

## Endpoint, dimension and reused-code checks

The final norm theorem branches on `p=0` before taking any reciprocal of `p`;
then `H=Z` directly. At `k=0`, `p>0`, it takes the exact sequence
`k_m=1/(m+1)` in the already proved small-base range and uses C14 and closedness
of real order. The limit is applied to each positive-dimensional compound
when needed. The degree-zero compound has dimension `choose n 0 = 1` and the
empty eigenvalue product is one. For every `j<=n`, the compound dimension is
positive. Internal claims that allow dimension zero reduce to the conventional
empty matrix, determinant and finite-product identities and do not introduce a
vacuous restriction on the final positive-dimensional theorem.

I inspected all 18 reused MI24 modules, including their actual minor/exterior
basis construction, sorted-spectrum permutation, full-real-power decomposition,
positive polar factor, inverse-order bridge and Furuta base proof. No source
theorem is replaced by an axiom. The copied Heron modules enter transitively
through the older combined `CompoundSpectral` module; MI28 uses its general
compound results and does not assume a Heron comparison in place of MI28.
Their original per-file authorship is retained. The reused source bytes match
the pinned source snapshot; the root's Git-object publication check is distinct
from my filesystem comparison and has not been independently rerun with Git.

## Numerical, trust and evidence checks actually performed

I wrote and executed `verify_integrity.py` in this directory. It is a read-only
Python audit of the candidate and saved evidence, not an independent Lean run.
Its successful output is `INTEGRITY.json`. It checked:

- all 83 snapshot files against the fixed manifest, with no unlisted files;
- the exact 52-module solution closure, excluding the trusted challenge;
- absence of proof placeholders, new axioms, unsafe/native proof commands or
  execution hooks in the proof sources, supplementing the complete manual read;
- all 52 actual successful source/command/log/output origins, their matching
  source hashes, and 92 retained evidence hashes, including saved reuse chains;
- one-thread, 4096 MiB compiler commands and completed successful origin records;
- all 20 standard axiom sets in the actual aggregate log and the 20 corresponding
  `#assert_trust kernel` commands in the successfully compiled source;
- the saved, independently elaborated challenge and solution type/universe
  arrays, which agree on all 20 contracts after binder-name erasure only;
- all edges of the saved proof-body routes from C20 through C15, normalized
  determinant equality, C02 and C01 to both closed LeanCert integer checks;
- unchanged bytes for all 18 reused source files and the three frozen boundary files.

The root's complete local record has SHA-256
`94a60f882bd02a9333db7e92a15b7045404b8ed43222dab744610abe60e01f39`;
the saved type/body comparison has SHA-256
`54cbbfe2497939fe78fbff9dd499b99c961316f6a22e36a98ba0fa7cc0256d45`.
The mixed local365 batch also contained unrelated MF14 failures; they are
explicitly recorded and do not lie in MI28's 52-module dependency closure.
I did not misclassify the whole mixed batch as successful.

The first version of my evidence script expected a LeanCert success log line
that this pinned version does not print. I read the actual aggregate log and
corrected the audit to use the source-bound silent assertion commands and
successful compilation, retaining that distinction here. No candidate proof
or compiler record was modified. The successful audit does not replay the Lean
kernel and is not the final Linux Comparator/default-kernel/sandbox check.

## Tau Ceti criteria and remaining publication work

Correctness/faithfulness and natural generality: approve. The universal result
uses concrete matrix objects and the unchanged parameter ranges. The auxiliary
conditional propositions have actual consumers and all their final premises
are discharged. The canonical target does not require a singular semidefinite
extension, so omitting that extension from this formal target is appropriate.

Proof quality: approve for this frozen standalone project. The long order
proofs are factored into named intermediate results and have comments explaining
their algebraic stages. Definition conversions identify the same explicit CFC
wrappers, matrix stars or scalar coercions; they do not hide a change of model.

Reuse and attribution: approve within the audited scope. The project relies on
pinned Mathlib CFC/order/AM-GM/determinant APIs and the unchanged existing MI24
machinery. I performed bounded local declaration-name and concept searches,
saved in `REUSE-SEARCH.json`, and checked the relevant pinned Mathlib signatures.
Those searches do not assert an exhaustive search of all external Lean projects
or Tau Ceti source. The code credits George Stepaniants with the requested
department/university and preserves Furuta/Fujii, Ghabries–Abbas–Mourad–Assi,
earlier MI24/MF05/MF06/MI22 code and AI-assistance attribution. No email is added.

Required before publication:

1. `lakefile.toml` currently selects only `Challenge` by default. Make a normal
   `lake build` build `Solution` (and check the canonical package locally), so a
   successful one-line build cannot mean only placeholder statement elaboration.
2. `lake-manifest.json` currently names the root package `NLAMI22`, while this
   package is `NLAMI28`. Correct the package metadata without changing the pinned
   dependency revisions.
3. Clearly identify `IMPLEMENTATION-PLAN.md`, `NUMERICAL_TARGETS.md`, and frozen
   draft-time comments as historical statement-first records. They currently
   contain text such as “UNIMPLEMENTED”, “No Solution.lean exists” and “No
   certificate has been computed”, which must not be presented as current status.
   Historical annotation in publication documentation can preserve frozen bytes.
4. Supply and independently review the final truthful `formalization.yaml`,
   reproduction instructions and Linux Comparator/kernel/sandbox evidence.
   These are known next gates, not missing mathematical lemmas in this candidate.

Optional maintenance only: `NormalizedHomogeneity`'s small local `hreal`
extensionality proof can use the existing
`RCLike.real_smul_eq_coe_smul (K := ℂ) r X`
(`Mathlib/Analysis/RCLike/Basic.lean:110`). It is a direct scalar-tower bridge;
this refinement does not affect the target or correctness. A later shared
library extraction could reduce the old combined compound/Heron import closure,
but preserving the authenticated reused bytes is appropriate for this release.

No new mathematical resolution or completed Lean-verification count is added by
this report. Any changed proof source needs a source-bound follow-up review and
matching local evidence; final publication/runtime evidence remains separate.
