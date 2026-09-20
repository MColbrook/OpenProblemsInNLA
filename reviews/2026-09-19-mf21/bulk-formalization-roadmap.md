# Completion update — 20 September 2026

The roadmap below is a preserved intermediate plan. Its outstanding mathematical dependencies have now been discharged in the canonical Lean project: actual root construction and endpoint smoothness; exact boundary determinant, signs and sine normalization; real uniform remainder bounds; actual ordered eigenvalue indexing; one smooth coefficient family; all-order bulk and lower-order global estimates; uniqueness and the trace obstruction.

A fresh source replay compiled all **82 canonical proof modules** with `--trust=0`, then independently audited the transitive axiom closure of **1,354 local declarations**. Every closure uses only `propext`, `Classical.choice`, and `Quot.sound`. `Solution.lean` does not import the separate trusted `Challenge.lean`; that specification elaborated independently with its five expected placeholders. The [replay receipt](verification/canonical-source-replay/result.json) and [complete audit output](verification/canonical-source-replay/logs/ReplayAxiomAudit.log) record exact source hashes. These are successful developer checks; at this update the separate Linux Comparator theorem comparison is still pending.

Two implementation refinements matter mathematically. First, exact binomial row operations factor the boundary determinant by $t^{m(m-1)}$, with $t=2\sin(\theta/2)$, avoiding an unproved removable quotient. The leading coefficient remains nonzero after this normalization, and conjugation proves the normalized error real. Second, the fixed-index low-order bounds follow directly from the implicit model's scaled limit and its uniform Taylor remainder, so the proof does not require an unformalized coefficient-vanishing claim. The trace limit is proved directly from the finite inverse column, Schur recurrence and beta-profile limit; the classical inverse-kernel theorem is not an assumed analytic input.

# Historical roadmap

# Bulk expansion: exact status and remaining proof

This records the dependency path for Sections 1–4 of the corrected manuscript. It is not a claim that MF21Challenge.FullTarget has been proved. All work remains local. The analytic determinant estimates and the eigenvalue indexing remain substantial outstanding obligations.

## Kernel-checked foundations

- **ToeplitzGram.lean** proves the actual signed-binomial Toeplitz matrix equals the Gram matrix of the rectangular finite-difference matrix, proves that difference matrix is injective, and proves positive definiteness, positivity of the actual sorted eigenvalues, and positivity of the determinant.
- **BulkSymbol.lean** proves smoothness and nonnegativity of the actual trigonometric symbol, its order-$2m$ bound at zero, a quantitative difference estimate, and its exact factorization by a continuous sinc factor tending to one.
- **BulkImplicit.lean** constructs the local smooth solution of $Y=x+h\eta(Y)$ from an arbitrary smooth phase, and proves existence and uniqueness globally under a contraction bound. Applying these results to the particular phase and obtaining uniform Taylor bounds on the compact interval are separate obligations.
- **BulkRoots.lean** constructs the actual stable root for each nontrivial unit-modulus $\omega$ and each $s>0$. It proves existence, uniqueness, nonvanishing, simplicity, the reciprocal characteristic equation, local complex analytic selection, and real smoothness of the canonical selected branch.

Each proved foundation has only the standard axioms propext, Classical.choice, and Quot.sound. None assumes a spectral expansion, a secular determinant, or the challenge target. Module compilation evidence is recorded in lean/verification as it is completed.

## Critical path still to close

1. **Endpoint stable roots and phase (Lemma 2).** Desingularize $r=1+t u$, obtaining $u^2+\omega t u+\omega=0$. At $t=0$ choose $u=-\kappa$, with $\kappa^2=-\omega$ and $\Re\kappa>0$. The partial derivative is nonzero, so the implicit-function theorem gives a smooth local branch. For small positive $t$, the identity
   $$
   |1+t u(t)|^2=1+t\bigl(2\Re u(t)+t|u(t)|^2\bigr)<1
   $$
   identifies this branch with the already constructed stable root at parameter $t^2$. Specialize $\omega_\ell,\kappa_\ell$, substitute $t=2\sin(\theta/2)$, glue the endpoint branch to the positive-parameter branch, and prove the uniform exponential decay estimate. Then construct each smooth phase from the factor $1-r_\ell e^{-i\theta}$ and prove its two endpoint values.
2. **Exact boundary determinant (Lemma 3, equations 13–16).** Convert the signed-binomial eigenvector equation to the order-$2m$ recurrence and the stated ghost conditions. Use the independent RecurrenceBasis.lean development to identify its solutions with linear combinations of distinct geometric sequences. This gives the zero-determinant criterion for the actual matrix. Expand that determinant over the bottom-row subsets, identify the two leading terms, and prove their normalization is the sine of the actual phase. This requires exact finite determinant identities, including signs; a numerical determinant check is insufficient.
3. **Uniform determinant remainder (Lemma 3, equations 11–12).** Establish that all characteristic-root differences have simple zeros at $\theta=0$ and distinct limiting slopes. Divide each Vandermonde product by its exact common vanishing order, extend the quotients smoothly, and prove their relevant denominators stay nonzero. Combine finite-product bounds with the stable-root decay and derivative bounds. Separately prove cancellation at $\theta=\pi$, where the two unit roots coalesce, and deduce the sharper endpoint remainder bound.
4. **Root location and sorted index (Lemma 4).** Prove monotonicity of $F_n$ for large $n$, exactly one determinant zero near each admissible multiple of $\pi$, exclusion of additional zeros near $\pi$, and the top-down index count. The root location alone does not identify the sorted eigenvalue index. Prove the circulant comparison used to bound the omitted small-index eigenvalues.
5. **Uniform expansion (Theorem 1(a),(b)).** Apply the already proved implicit-function construction to the actual smooth phase; prove compact uniform Taylor bounds; bound the difference between the determinant root and the implicit root by the exponentially small remainder. Establish the vanishing order of each coefficient at zero and combine the small-index estimates with the bulk estimates at the logarithmic-square cutoff.

Only after those steps are proved can the coefficient-uniqueness and trace-obstruction modules be connected to the actual expansion and the full challenge theorem. The conditional implications already checked do not eliminate any of these spectral or analytic obligations.

## Available mathlib support

The pinned mathlib has the smooth implicit-function theorem (Analysis.Calculus.ImplicitContDiff), Banach fixed-point theorem, Vandermonde determinant and invertibility, linear-recurrence solution space and initial-value equivalence, Hermitian eigenvalue theory, and Taylor remainder estimates. It does not supply this Toeplitz secular determinant or its endpoint-uniform remainder estimate as a ready-made result. Those are the central custom formalization tasks.
