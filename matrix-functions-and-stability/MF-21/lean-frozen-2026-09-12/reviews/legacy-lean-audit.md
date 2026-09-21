# Independent MF-21 Lean statement and soundness audit

Date: 20 September 2026. Reviewer scope: independent inspection of the canonical statement, the actual manuscript, Lean definitions and theorem hypotheses, and available verification records. AGENTS.md was read. No Lean compiler, Lake build, Comparator, or GitHub workflow was run by this reviewer. The shared Lean source and manuscript were not edited.

**Verdict: BLOCK — the current scratch project is not a verification of MF-21 and must return to the statement gate.** It contains useful foundational proofs, but its concrete target specialization has an indexing defect, several advertised asymptotic interfaces cannot be instantiated with the manuscript's data, and one trace theorem obtains a false conclusion about the target from already inconsistent assumptions. These are statement and applicability defects; they are not evidence of a Lean kernel inconsistency. The appropriate completed-target count remains zero.

The subsequently supplied pinned REFEREE_STANDARDS.md was read. This report serves its source-fidelity/correctness lane, with additional applicability and evidence observations explicitly distinguished below. The standards file SHA-256 was e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1.

## Frozen inputs and evidence

All line references below refer to the frozen files in [audit-lean-snapshot](./audit-lean-snapshot/). The snapshot matches the shared sources at the time of this audit.

| Input | SHA-256 |
| --- | --- |
| MF21.lean | 952b956736971284f0cdba9102757a3be6c39013634c9d67f7e32daec74a790b |
| formalization.yaml | dd23a6de60e917ea920829844a8ae5535ea88f4b86f60712a970fb967064b438 |
| solution.md | 6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa |
| canonical-README.md | 1aac38ed3c7a83dfc3dddb4beeec26fcf117f23f5789b2a374c1332ba4cf359f |
| recorded local build log | dc05c26ef9873c97bbc629a4f9d7f2861144fac985f08d7a6894487de7c9e009 |
| recorded Lake MF21.trace | 02adf50afc25b21005d0fe885af07ce5d3c5f29248e551057f3c87b262e351d6 |

The [evidence manifest](./audit-lean-snapshot/evidence.json) records original paths, further hashes, byte sizes, and source/snapshot equality. The preserved build log is [build-spectrum-accessor.log](./audit-lean-snapshot/build-spectrum-accessor.log).

The canonical target is README lines 16–39: for every integer m >= 3, one common family of continuous coefficients d_0,...,d_{2m}, independent of n and j, satisfies all three parts, using the increasing, multiplicity-counted eigenvalue lambda_(n,j) with 1 <= j <= n and the mesh j*pi/(n+2). The critical bulk threshold is fixed as ceil(log(n+2)^2). The manuscript's claimed theorem, lines 21–29, addresses that same target. This audit does not recheck the manuscript's external sources or independently certify its entire informal proof.

## Findings requiring correction

### 1. Critical: the concrete target uses the wrong eigenvalue accessor

MF21.lean lines 388–389 define toeplitzEigenvalueAt as a **zero-based** accessor: it returns sorted eigenvalue number j+1 when j < n and returns zero otherwise. But lines 1043–1056 specialize the **one-based** target predicates to the unshifted expression toeplitzEigenvalueAt m n j.

Consequences on the declared range 1 <= j <= n:

- j=1 refers to the second eigenvalue;
- the first eigenvalue is omitted;
- j=n returns the artificial value zero.

This is more serious than an asymptotically small shift. The p=0 hypothesis at lines 1048–1049, together with d_0 = symbol on [0,pi], would imply

    |0 - symbol m (n*pi/(n+2))| <= D/(n+2)

for all sufficiently large n. Its left side tends to 4^m and its right side tends to zero. Thus this specialization's premises cannot hold for the required coefficient family. Its theorem is a valid implication with impossible intended premises, not a Toeplitz target theorem.

The correct accessor already exists at lines 3453–3458: toeplitzEigenvalueOneBased selects j-1 after checking 1 <= j <= n. Its characteristic-determinant lemma, lines 3574–3587, is correctly indexed. The newer toeplitzEigenvalueAt determinant and spectrum lemmas at lines 3593–3611 also correctly use j-1; they do not repair the unshifted target specialization.

**Correction:** use toeplitzEigenvalueOneBased consistently in the canonical target and all analytic contracts. Alternatively, retain the internal zero-based accessor and insert j-1 explicitly everywhere an externally one-based j occurs. Prove and retain the bridge on 1 <= j <= n; do not redefine the existing zero-based accessor silently.

### 2. Critical: the bulk bridge assumes the forbidden global critical estimate

Lines 5683–5686 assume, for every j <= n and all sufficiently large n,

    |R_(2m,n,j)| <= C*exp(-c*j)/(n+2)^(2m+1),  c>0.

Because every natural j is nonnegative, exp(-c*j) <= 1 without any logarithmic threshold. This hypothesis immediately implies UniformCriticalBoundExact with constants C,N_0. It therefore contradicts the no-uniform-critical-bound conjunct of MF21Target for the same eigenvalue sequence and coefficients.

The extra threshold assumption at lines 5687–5688 is also automatic for every n, with N_1=0, solely from c>0 and nonnegativity of a natural ceiling. The argument at lines 5826–5838 does not establish the scale gain needed in the manuscript.

The two-error versions, lines 5754–5791 and 5845–5860, inherit this problem. They assume both the spectral approximation error and Taylor error already have an exponential factor and the final critical denominator power. Their sum again proves the prohibited uniform critical estimate.

The manuscript instead proves, only for j >= J, at lines 298–303, equation (25),

    |lambda_(n,j) - g(Y(x_(n,j),h))|
      <= A*h^(2m)*j^(2m-1)*exp(-c*j).

Its Taylor error at lines 282–287, equation (23), is O(h^(p+1)) without an exponential factor. At p=2m that Taylor error is O(h^(2m+1)). These are different contracts.

**Correction:** replace the advertised application with the exact obligations stated below. The existing conditional inequalities may remain archived as generic facts, but must not be counted as verification of the manuscript's critical bulk step.

### 3. Critical: the trace theorem assumes a contradiction before introducing the target

Lines 5868–5891 define not_mf21_target_of_trace_series_obstruction. Its assumptions yield two limits of the same real sequence:

- dominated convergence, the trace identity, and hkernelLimit yield kernelLimit;
- hspectral yields spectralLimit;
- hne asserts that these limits differ.

They are inconsistent independently of eigenvalue, d, m, or MF21Target. The proof makes this explicit: line 5890 introduces _htarget and never uses it; line 5891 invokes uniqueness of limits. The same premises could prove any proposition.

Moreover, the stated conclusion is logically opposite to the manuscript's intended use. The manuscript assumes a uniform critical estimate for contradiction (lines 345–355), derives the fixed-index limits from that assumption, and concludes **not UniformCriticalBoundExact**. It does not disprove MF21Target, whose last conjunct is precisely that non-uniformity.

**Correction:** the unconditional kernel limit and the spectral-series limit derived under a hypothetical uniform bound must remain separate. The conclusion must be

    not UniformCriticalBoundExact lambda_one_based d m.

The fixed-index spectral limit and the treatment of j=1 in the majorant must be derived after introducing that uniform-bound hypothesis. Merely changing the name/conclusion while keeping all currently inconsistent premises would not establish new mathematics.

The countable-series exponential-majorant specialization at lines 5080–5096 is also not the manuscript's domination argument. The limiting terms in equation (31) decay polynomially, as (j+a)^(-2m), and cannot be bounded for all j by a fixed polynomial times exp(-c*j). Use the actual polynomial majorant from manuscript equation (22), with a separately controlled first index.

### 4. High: the determinant-decay chain excludes the exterior roots

Lines 5511–5519, 5551–5559, 5567–5576, 5975–5987, and 6021–6034 require, for **every** root index i,

    norm(roots i) <= beta i <= 1.

The manuscript's boundary determinant has m-1 exterior roots q_l = r_l^(-1), each of modulus strictly greater than one for positive theta; see manuscript lines 142–146 and 192–200. Thus these hypotheses cannot hold for its actual root vector.

These helpers bound raw determinant monomials. The manuscript's decaying objects are the **normalized, grouped Laplace terms** in equation (18): a_S(theta)*b_S(theta)^(n+m), after dividing by the leading factor involving Q^(n+m+1). Exterior growth must cancel in the normalization. A bound for contractive raw roots does not implement that cancellation.

The later reciprocal/exponent-gap lemmas at lines 6096–6163 are valid scalar ingredients, but no theorem shown connects them to a normalized expansion of the actual determinant.

There is a related endpoint issue at lines 5911–5918: a fixed positive lower bound on the raw normalizer over [0,pi] is unavailable. The manuscript explicitly says its numerator and denominator vanish to order m(m-1) at zero (line 211). Bounds on [delta,pi] for fixed delta>0, or for fixed n, do not supply the uniform endpoint/n-dependent bounds needed in Lemma 3. Cancellation of the common vanishing factors is essential.

**Correction:** formalize equation (14) with inherited subset order, evaluate the two dominant subset coefficients, and prove the smooth extension and bounds of the ratios in equation (18). Any alternate normalization must be defined and its equality to the original determinant proved before applying contractive-factor estimates.

### 5. High integration hazard: determinant permutations and bottom images use opposite conventions

The determinant expansion at lines 5330–5337 has monomials

    product_i boundaryMatrix m n roots (sigma i) i.

Here sigma maps a **column/root index to a row index**. Therefore the roots assigned to bottom rows are sigma^(-1)(bottom), expressible as bottomRowIndices.image sigma.symm.

The classification at lines 6486–6492 instead concerns bottomRowIndices.image sigma. It is a correct combinatorial statement for an arbitrary permutation, but it is not the bottom-root set of the displayed monomial for that same sigma.

Concrete m=3 example: bottom={3,4,5}, stable={0,1}, oscillatory={2,3}, exterior={4,5}. Let sigma be the cycle 0->3->2->0, fixing 1,4,5. Its image of bottom is {2,4,5}, a dominant set according to the classification. But the actual bottom-root set of the determinant monomial is its preimage {0,4,5}, which contains a stable root.

**Correction:** instantiate the classification with sigma.symm, or rewrite the entire determinant expansion in a row-to-column convention and prove the reindexing/sign identity. I found no completed theorem already applying this mismatch, so this is an interface defect to prevent during integration, not a claim that the standalone combinatorial lemma is false.

### 6. Medium: retained target/recurrence wrappers can be mistaken for substantive progress

- The legacy MF21Statement at lines 972–977 permits an arbitrary existential bulk threshold. Taking threshold(n)=n+1 makes its bulk quantifier vacuous. It also includes j=0 in the uniform ranges (lines 948–968). Keep it separate from the canonical exact target or retire it.
- The assembly theorems at lines 1031–1056 and 1075–1096 assume all substantive conclusions. They do not construct coefficients or establish any Toeplitz asymptotic estimate. The concrete version also has finding 1's indexing defect.
- The companion-power obstruction lemmas at lines 2600–2743 and 4842–4854 assume an exact identity or lower bound linking the scaled remainder to growing companion powers. The manuscript uses a trace contradiction and proves no such companion-power identity. These are conditional templates, not proofs of Part 3.
- At lines 4809–4838, all 2m listed roots are selected from one quadratic with one coefficient a. There are at most two distinct roots. For m>=3 the boundary determinant consequently has repeated columns and is zero independently of the Toeplitz spectral problem. A nonzero coefficient vector may represent the identically zero mode. The equivalence is valid, but does not establish the intended order-2m characteristic-root/eigenvector bridge.
- The generic boundary-to-eigenvector contracts at lines 3279–3358 assume the all-row eigen-equation as hmode. This is an acceptable explicit interface, but it cannot be described as discharging the general-m recurrence-to-boundary spectral identification. The concrete all-row m=3 work is a separate, useful accomplishment.

## Correct canonical main statement

Using the existing definitions, the intended proposition can be represented by the following statement-only definition:

    def CanonicalMF21 : Prop :=
      forall m : Nat, 3 <= m ->
        exists d : Nat -> Real -> Real,
          MF21Target
            (fun n j => toeplitzEigenvalueOneBased m n j) d m

This is schematic notation, not a compiled declaration from this review. The exact Lean syntax is already available from the corresponding existing types. A completed proof must establish this existential coefficient-family statement for every m>=3. It may prove the stronger smoothness claimed by the manuscript, but the canonical contract requires continuity only through order 2m.

The exact target predicates at lines 987–1021 correctly express the published ranges and coefficient restrictions when supplied with the correct eigenvalue function. The fixed bulk threshold implicitly has positive index because log(n+2)>0. The infinite function family d is a harmless representation of the finite family when only indices <=2m are constrained.

For complete statement faithfulness, also retain an explicit identification of the real cosine Fourier coefficients at lines 99–101 with the canonical complex exponential coefficients: the omitted sine integral vanishes by parity. The mathematical equivalence is straightforward, but a real cosine definition alone is not the formal identity.

## Reusable obligations aligned with the manuscript

Set t=n+2, h=1/t, x_(n,j)=pi*j/t, lambda=lambda_one_based, and

    base(n,j)=symbol m (Y(x_(n,j),h)).

All constants below are independent of n and j, but may depend on m and the indicated order.

1. **Phase and spectral approximation, exactly equation (25).** Prove A>0, c>0, N, and J>=1 such that, for n>=N and J<=j<=n,

       |lambda(n,j)-base(n,j)|
         <= A*j^(2m-1)*exp(-c*j)/t^(2m).

   Do not extend the statement to j<J. Do not increase the denominator power to 2m+1 before restricting to the logarithmic bulk.

2. **Uniform Taylor construction, exactly equation (23).** For each p<=2m, prove B_p>0 and N_p such that, for n>=N_p and 1<=j<=n,

       |base(n,j)-expansion d p n j| <= B_p/t^(p+1).

   There is no exponential-in-j factor here. Prove the d_k are constructed from the same Y and are continuous (indeed smooth), with d_0=symbol on [0,pi].

3. **The actual logarithmic scale gain.** For every c>0 and natural q, prove

       exists N, forall n>=N, forall j>=ceil(log(n+2)^2),
         (n+2)*j^q*exp(-c*j) <= 1.

   This is a useful analytic subgoal, unlike exp(-c*j)<=1. A proof route is to split the exponential into two factors with rate c/2. Polynomial-times-exponential decay gives j^q*exp(-c*j/2)<=1 for large j. The growing logarithmic-squared threshold eventually implies j>=(2/c)*log(n+2), making the other exponential at most 1/(n+2). Combine with the eventual inequality threshold>=J.

   Obligations 1–3 yield the critical bulk bound with constant A+B_(2m), on the required range. They are consistent with failure at any fixed small index.

4. **The finite low-index range and lower orders.** Supply the actual small-index eigenvalue estimate and endpoint coefficient bounds (manuscript lines 259–306). For 1<=j<J, both lambda_(n,j) and the p=2m-1 expansion are O(t^(-2m)). For j>=J, use the bounded function j^(2m-1)*exp(-c*j), obligation 1, and Taylor order 2m-1. Then derive the lower orders by boundedness of the omitted coefficients. A global approximation-to-base assumption covering j<J would bypass an unproved step.

5. **The non-uniformity argument must depend on the hypothetical uniform estimate.** Under

       hU : UniformCriticalBoundExact lambda d m,

   and the already established coefficient construction, derive for every fixed j>=1

       t^(2m)*lambda(n,j) ->
         (pi*j + eta(0))^(2m)
         = pi^(2m)*(j+(m-1)/2)^(2m).

   Continuity of arbitrary d_k alone does not give this formula. Use the actual critical Taylor approximation, the equation Y=x+h*eta(Y), eta(0)=(m-1)*pi/2, and symbol m y=(2*sin(y/2))^(2m). The finitely many n<j are irrelevant to the limit but must not create an indexing change.

6. **Concrete trace sequence and domination.** For a zero-based summation variable k, define the spectral terms using j=k+1:

       f(n,k) =
         if k+1<=n then 1/(t^(2m)*lambda(n,k+1)) else 0.

   Prove their sum equals t^(-2m)*trace(A_n^(-1)), including invertibility/positive eigenvalues. Under hU their pointwise limits are

       g(k)=1/(pi^(2m)*(k+1+(m-1)/2)^(2m)).

   Use a summable polynomial bound for k>=1 from interlacing and the fixed-index limit to bound k=0 eventually. The kernel limit is established unconditionally from the actual inverse-kernel theorem. Prove the two explicit constants differ. Only then does a contradiction conclude not hU.

These are proof obligations, not additional verification claims.

## Minimal useful next formalization

First repair the public statement/accessor contract. That repair itself is bookkeeping and must not increase the completed-verification count.

For a fresh bounded analytic module, the most useful progress is the **concrete fixed-index scaling step** in obligation 5: from the actual implicit phase equation and endpoint phase value, derive the limit of t*Y; use the concrete sine-power symbol to derive the limit of t^(2m)*symbol m Y; then connect the critical Taylor approximation and hypothetical uniform bound to the one-based eigenvalue limit. Make all as-yet-unproved construction assumptions explicit. A module proving only uniqueness of limits or another conjunction assembler would not advance the missing mathematics.

The alternative small analytic task is obligation 3's uniform log-squared absorption estimate. It genuinely supplies the missing factor t and can be reused in the correct bulk proof. Neither module would by itself constitute full MF-21 verification.

For the larger determinant track, the next substantive milestone is the actual normalized subset expansion with endpoint cancellation, not additional raw contractive-root inequalities.

## Verification claims and retained scope

The following observations are supported by the inspected files:

- formalization.yaml line 2 correctly says partial; lines 277–281 acknowledge the main remaining analytic work.
- The source SHA in YAML line 286 exactly matches the inspected source. The recorded local log says Built MF21 (33s) and ends Build completed successfully (3730 jobs). This is evidence of a recorded local build, not a fresh run by this reviewer.
- The Lake trace records Lean 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, the source path, and compiler invocation. The manifest pins mathlib to 0df444a360eaa60ab8c11dca51a86af692955474 and LeanCert to 621a43d7cf21f87872392a01e874f2f1dbddc926. The current shared package checkouts have those HEADs and no tracked/untracked modifications according to git status --porcelain.
- The visible source uses kernel-mode LeanCert at lines 26 and 35–36. A text scan found no sorry, admit, axiom, unsafe, or native_decide tokens in MF21.lean. This scan is not a replacement for an axiom/dependency audit or Comparator.
- YAML line 287 explicitly says Comparator not_run. No real Comparator, kernel/sandbox GitHub run, or run ID was established by this audit.

Limits of that evidence:

- The recorded command lake build MF21 and the saved compiler command do not show an explicit one-thread/4096 MiB resource envelope. Such limits could have been applied externally; the available records do not establish or refute that. The total Lake job count does not mean concurrent compiler processes.
- The saved build log does not itself contain a cryptographic source hash; the exact SHA association is supplied by the metadata, which matches the current file. This review did not independently reproduce the build.
- YAML lines 288–291 contain a narrow review scope and a bare OFFSET_REVIEW_STATUS:0 marker, not a full source-matched review report.
- YAML line 295 lists RootsFocused.lean with an ambiguously associated hash de12aea88e4c361b876257f476081e93e0f95b09199e1f34b1b6816b68120408. That hash matches neither the audited MF21.lean nor the currently inspected RootsFocused.lean, whose SHA is 8b6af06fe19b82e2126785d4c315c926b08e42ada3b1fb812e1f460994d308cc. It may refer to an earlier source snapshot, but the record must identify that snapshot and justify reuse for the current source. The review file itself consists of examples applying the existing root lemmas; it does not by itself document an independent statement/proof audit of the complete project.

The verified-scope descriptions should be corrected or narrowed in particular at YAML lines 27–38 (raw determinant and bulk/trace interfaces), 178 and 269–271 (assumed companion-power relations), and 274 (the incorrectly indexed concrete target assembly). Lines 272 and 276 concern the shifted j-1 use of the zero-based accessor, not its unshifted use in the target. No passed claim should be extrapolated from those descriptions to the original three-part conjecture.

Useful foundational content should be retained with its exact scope: the symbol identity, Fourier recurrence and finite bandwidth, Hermitian/positive-semidefinite spectral facts, sorted and correctly one-based accessors, pointwise strict stable-root contraction, finite determinant/kernel identities, and concrete all-row m=3 recurrence/eigenpair bridges. These do not yet prove the general-m phase indexing, uniform normalized determinant residual and derivative bounds, coefficient construction, low-index/interlacing estimates, inverse-kernel trace limit, or explicit irrationality contradiction.

No completed original mathematical target or complete Lean verification is added by this audit, by the assembly wrappers, or by the proposed statement repair.
