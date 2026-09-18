# MI-28 independent statement-first source review

**Approve the exact statement source, subject to the separate elaboration and
freeze gates.** I found no semantic blocker and request no change to the
proposed definitions, twenty headers or Comparator configuration. This is not
an elaboration result, an approval to begin implementation, a proof review, a
Linux result, or publication/count acceptance.

I am Codex agent `/root/mi24_full_referee1`, not the statement author
`/root/nm04_final_referee1`. I read the complete canonical README and analytic
solution, all proposed Lean source, the numerical and implementation plans,
and the packet's provenance/status records. The exact 16-payload checkpoint is
bound by manifest
`f34964a178d08ded6e9f7d729f70da606c9edac8475d344e7a5d2c00e1c1f1fd`.
I did not read root's independent statement findings before this verdict. I
did not edit the checkpoint or run Lean, Lake, Comparator, Git or publication
tools. The 20 `sorry` bodies are intentional statement placeholders, not a
purported completed proof.

## Full-target fidelity and vacuity checks

`DeterminantComparison` quantifies over every natural dimension with `1 ≤ n`,
every complex positive definite pair, every real `k ≥ 0`, and every real
`0 ≤ p ≤ 2`. It retains the literal ordered expressions
`det(A^k + |AB|^p)` and `det(A^k + A^p * B^p)`, concludes that both complex
determinants have zero imaginary part, and compares their real parts in the
correct direction. There is no commutativity, integer-exponent, fixed-dimension,
bounded-k, or extra spectral assumption. Neither Furuta nor an order/norm
comparison is a premise of C20. Reality and strict positivity are also
conclusions of C19, which is valid for all real exponents on PD inputs.

The definitions refer to actual Mathlib objects. `Mat n` is the complex matrix
type; matrix order is the Löwner order because the scoped instance means that
the difference is positive semidefinite. `CFC.abs X` is the positive square
root of `star X * X`, including nonnormal products. `CFC.rpow` is actual spectral
functional calculus, with its zeroth power equal to identity on nonnegative
inputs. The PD premises and the proved positivity of the product modulus keep
all negative powers inside the intended invertible positive domain. A default
value of functional calculus outside that domain is not being used to weaken
the target. `operatorNorm` takes the norm of the continuous linear map on
complex Euclidean space, not an arbitrary or entrywise matrix norm.

`sortedSpectrum` transports Mathlib's descending `eigenvalues₀` along the
cardinality equality for `Fin n`. I checked the antitone and characteristic-root
multiset interfaces. Multiplicity and order are preserved; no arbitrary
permutation replaces the decreasing list. `WeakLogMajorized` includes all
prefix lengths through n, and `LogMajorized` additionally demands exact equality
of total products. The redundant full-length inequality and the empty-prefix
identity do not weaken the usual definition. C15 existentially supplies both
positive-definiteness proofs before constructing the spectra. These witnesses
cannot be replaced by false antecedents, and proof irrelevance prevents their
choice from changing the spectral data.

The `OrderImplication` predicate is the universal order implication used in the
canonical proof. Its conditional input is made applicable in C11 by positive
norm scaling; it is not a disguised final assumption. C09's swapped premise is
local and universal over all pairs. For the only remaining branch in C10,
`p < k/(k+1) < k ≤ 2`, the swapped assertion is supplied by C07 when `k ≤ 1`
and by C08 when `1 ≤ k ≤ 2`. Thus there is no circular use of C10 to establish
its own swapped premise. Identity matrices give nonempty examples of the PD
input domain at every permitted dimension; the final theorem is not vacuous.

## Contract and endpoint checks

`BINDINGS.json` contains an independent semantic disposition and exact header
hash for each of C01–C20. The following are the material checks.

- C02 keeps the noncommuting order `B * A² * B`. If `D = |AB|`, then
  C03 uses `B * D⁻² * B = A⁻²`; the positive root is `A⁻¹`.
  Reversing the input factors would change the assertion.
- C04's matrices are positive congruences by invertible powers for arbitrary
  real k,p. The normalized determinant factors in C18 are therefore genuine
  positive spectra, even though the original right sum need not be Hermitian.
- C05 and C06 cover all nonnegative real sandwich parameters. They do not
  substitute MI24's bounded parameter slice. Restricting the inner exponent to
  `a ≥ 1` covers every required `a = 2/p`; no unused broader Furuta theorem is
  required. `a+r` and `(1+r)q` are positive under the displayed assumptions.
- C07's range is exactly canonical Lemma 2. Its explicit `p>0` also follows
  from `k>0` and the lower bound, so it creates no new restriction. C08 includes
  p=1 and p=2. All intermediate divisions in the plan have strictly positive
  denominators. The inequalities for s and the two Löwner–Heinz exponents
  follow symbolically from the displayed bounds, not a parameter grid.
- C11 covers `0<k≤2`; C12 covers all `k≥2`. The common edge k=2 is harmless.
  Normalization uses the positive norm of Z, justified by n≥1 and PD, and
  C13 scales by a strictly positive real scalar.
- At p=0, H and Z both equal `A^(-k)` and the original determinant sums both
  equal `A^k+I`. At k=0, p>0, the proposed sequence `1/(m+1)` approaches zero
  through the already proved small-base range. C14 gives the required norm
  continuity for each fixed compound pair. No unproved continuity of sorted
  eigenvalues need be assumed.
- The swap includes p=k: the second Löwner–Heinz exponent is zero and the
  resulting comparison is identity against identity. The proof must retain
  that endpoint. Dimension one, repeated eigenvalues and every compound degree
  j≤n are included. Degree zero gives an empty product; positive permitted
  compound degrees have positive dimension.

For the large-base branch, I directly inspected the author-uploaded primary
paper's Lemmas 2.1–2.5 and Lemma 2.5 proof. Its range is `0≤t≤s≤K`; substituting
`X=A⁻¹, Y=B, s=2, t=p, K=k` gives the asserted positive representatives H and
Z. The two additional norm inequalities named in the plan correspond to its
Lemmas 2.2–2.3. Their proofs remain required internally.
[Ghabries–Abbas–Mourad–Assi, author manuscript](https://www.researchgate.net/publication/342908148_A_proof_of_a_conjectured_determinantal_inequality).

I also read the retained Fujii text at printed p.30. The substitution extending
the boundary theorem from r1 to `r1+(1+r1)t`, `0≤t≤1`, matches the plan. An
induction on a natural upper bound covers every finite nonnegative real r.
This is a valid proposed extension, not an existing implementation.
[Fujii, Theorem 1.3 proof](https://emis.muni.cz/journals/AFA/AFA-tex_v1_n2_a4.pdf).

C16 has the correct tangent direction: for the convex function
`g(x)=log(1+exp x)`, its tangent at `log a` lies below its value at `log b`.
Rearranging gives exactly C16. In C17, the positive weights `a/(1+a)` decrease
when a decreases. Prefix-product inequalities give nonpositive prefix sums of
`log a-log b`, so the planned existing weighted-prefix-sum lemma applies.
No order hypothesis on b is needed. The n=0 scalar helper has both products
equal to one. C18 uses determinant multiplicativity and `det(I+UV)=det(I+VU)`
to account for the non-Hermitian right sum. Positive determinants of PD powers
and `I+H`, `I+Z` give the real-order interpretation in C19/C20.

## Numerical obligation and remaining proof work

C01 is sound and minimal: the exact dyadic fact `0 < 1/2 < 1`. No dimension,
matrix-entry, eigenvalue or real-parameter interval sampling is useful here.
There is a substantive CFC domain condition for this certificate to supply:
the pinned `CFC.rpow_rpow` requires the inner exponent to be nonzero, and
`CFC.rpow_rpow_of_exponent_nonneg` requires nonnegative exponents. The positive
half establishes those conditions when composing the half power with the square
in the modulus/root route. The bound also gives the admissible half exponent
for Löwner–Heinz. This is mathematical domain evidence, not a decorative
numerical statistic.

There is no proof body yet, so **actual certificate consumption is not
verified by this statement review**. The implementation must pass C01 to a
genuinely required CFC half-power side condition and retain an actual final
proof-body route through the checked LeanCert certificate. An unused `have`,
an artificially added assumption, or a syntactic theorem-name match will not
suffice. Existing identities such as `CFC.abs_sq` should be reused where they
fit; they should not be reproved merely to manufacture a dependency. No larger
certificate or additional computation is requested.

The packet explicitly leaves the unbounded Furuta extension, the internal
large-base comparison, scalar transfer and endpoint/determinant assembly
unimplemented. These honest gaps do not make the proposed theorem statements
incorrect. They are mandatory proof work before completion can be claimed.
This source approval must not be cited as evidence that those gaps are closed.

## Standards, provenance and actual checks

I applied the pinned Tau Ceti correctness, generality, proof-quality, reuse and
attribution guidance at `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`.
Proof quality cannot be approved for absent proof bodies. The bounded reuse
inspection located the existing CFC square/power/order APIs, actual descending
spectrum and Euclidean map APIs, and MI24's scalar prefix helper. The plan
recognizes MI24's limited Furuta coverage and preserves source attribution.
I did not claim a search of an unavailable pinned mathematical Tau Ceti
repository or an exhaustive library theorem search.

George Stepaniants's contribution, department and Caltech affiliation are
retained; Ghabries–Abbas–Mourad–Assi, Furuta, Löwner–Heinz, Fujii and the reused
formal sources are credited. The selected canonical target is the retained PD
formulation. The source's broader PSD remark is not silently claimed as a new
formal result. No email or bulk primary paper is copied into this review.

I actually replayed `python3 verify_packet.py --live --sealed`: **PASS, 813
checks**, tool completion `ecb120`. This checks all 16 payload hashes, referenced
external sources and the 223 retained complete-tree path scans. The independent
`verify_review.py` additionally authenticates this review's complete bindings,
every header, the original-audit links and canonical Git blob identities.
Its execution receipt is kept outside the sealed review manifest to avoid
self-hash cycles. These are read-only Python checks, not Lean or Comparator.

The public records have a dated, bounded scope. The 30 conservative tree matches
are archived MI28 directory/README copies inside MF07, not target Lean sources.
The retained PR searches report the existing informal resolution and a catalog
PR. I did not perform a new branch/PR audit or establish universal novelty.
The only new network read in this review was the primary-paper check described
above. All 16 packet payloads are bound; the public-tree observation rows were
authenticated and rescanned programmatically, not semantically read file by
file across every repository tree.

Root's actual statement-only elaboration of these exact bytes, or a separately
reviewed successor delta, and the second independent statement approval are
still required before the coordinator freezes the statements. This review
neither invokes the official Tau Ceti engine nor claims external human review,
proof completion, final Linux acceptance or a count change.
