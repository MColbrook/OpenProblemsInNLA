# Independent review: exact normalization and determinant remainder

Verdict: **APPROVE** the new assembly proofs and their correspondence to
manuscript Lemma 3, with the independent-authorship scope below. No material
statement or proof defect found. The MF-21 Target remains incomplete and no
Comparator check is claimed.

Reviewer: `/root/mf21_restart_lean_audit`, 20 September 2026. Both reviewed
modules were authored by the coordinator, not this reviewer. No source edits
or compiler processes were performed by the reviewer. The pinned standards
have SHA256 `e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Exact files and successful local evidence

| Artifact | SHA256 |
|---|---|
| `MF21Restart/LeadingNormalization.lean` | `74e5df08f291842541efcc6c92ca718121066d15a047daf213303bc4a8571de3` |
| `LEADING_NORMALIZATION_STATEMENTS.md` | `e6f878d869119c2a1eac5e5fbfdcfb7c59dcbc472f919be100371dce78f7c4af` |
| `evidence/logs/leading-normalization-02.json` | `7bae8b67be3e48a3a8df326a9cfc31b8d9b9c6e7587efc5006e0f8f4b45c4c3f` |
| `evidence/logs/leading-normalization-02.log` | `fe8b6a7d3546c92cfab7a36af13cc2d26d651703ca3fd3fadfe05e41cba44ea3` |
| `.lake/build/lib/lean/MF21Restart/LeadingNormalization.olean` | `31e737cdee73c9b535f3194f6856f8f89432bfa8e5b9793f48b6ade8a28f42d6` |
| `MF21Restart/DeterminantRemainder.lean` | `3ff379de253810a3edaf355a243e26981c46d0052ca636aac5ace9b82bb6f318` |
| `DETERMINANT_REMAINDER_STATEMENTS.md` | `3f0e4ab188aed679b624d29fb439ae2f2f508fdabddfcbe19ef61ebf5c17d242` |
| `evidence/logs/determinant-remainder-02.json` | `4eaef2900fee304fbd2361701e57b4706c9a0220f2d295443f06a527f50c0463` |
| `evidence/logs/determinant-remainder-02.log` | `f0a52c88cd30086f80bff8698ee346eccf03c148304f0cfa095e1bc090b08809` |
| `.lake/build/lib/lean/MF21Restart/DeterminantRemainder.olean` | `8dfed6a9442c2890f1b925bd34e144e4d5e8b2a84946a9751b7475c9d4e3f5c6` |

The reviewer independently recomputed every hash above and verified both
JSON records match the current source/log/output triplets. Each records
exit_code=0, source_unchanged=true, `LEAN_NUM_THREADS=1`, and the actual
command `lake env lean -j1 -M4096 -o <corresponding output> <corresponding
source>`. The logs contain six and nine axiom reports respectively, all
restricted to `propext`, `Classical.choice`, and `Quot.sound`, with no
`sorryAx` or error line. The warnings concern unused tactics or a redundant
simp argument and do not weaken the statements.

The comparison manuscript is `original-proof/solution.md`, SHA256
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`:
lines 112–138 state (9)–(12); lines 176–215 derive the normalization and
remainder. The original symbol/eigenvalue definitions remain unchanged at
`Definitions.lean` SHA256
`35a74047a81a9b7526e9bf039880ca8f07ae33314e2b5b960ab254e02fca4b51`.

## Phase and coefficient normalization

`LeadingNormalization.lean:16–23` factors the existing multiplier as
`U=z^(m-1)*exp(2*i*psi)`. The sign of psi is positive here. In contrast,
lines 79–88 prove the leading quotient is
`z^(n+m)/U=exp(i*F_n)`, where
`F_n=(n+1)*theta-2*psi=(n+2)*theta-eta`. The conversion of natural m-1
to real m-1 is justified by m>=1. The proof preserves the manuscript's
minus sign for psi and uses the actual phase definition from
`PhaseMonotonicity.lean:35–45`, SHA256
`0c0e3034173e4a00103d31eb702356c037f71617ed8e3c4e67f7c69b3b7f7300`.

Lines 25–60 combine the actual plus coefficient
`-V(R)V(O)Q*z^(-(m-1))*conj(f)^2` with `2*i*U*Q^(n+m)`.
The two powers of z cancel, and
`conj(f)^2*exp(2*i*psi)=normSq(f)` follows from the already proved
f/conj(f) identity with its denominator nonzero. Thus the resulting
normalizer is precisely `(-2*i)V(R)V(O)Q^(n+m+1)|f|^2`.
Neither the exponent n+m+1 nor the overall negative sign is lost.
There is no replacement of a sum of individual arguments by a principal
argument of the product.

Lines 62–77 prove `Aminus=-Aplus*U^2`. Lines 90–134 combine this with the
actual root products z*Q and z-inverse*Q and the identity
`exp(iF)-exp(-iF)=2*i*sin(F)`. The result has **plus** `N*sin(F)` on the
right. The proof does not choose a sign to fit a zero set after the fact.
The interval is 0<theta<=pi, and every division is supported by proven
nonvanishing of the relevant root, multiplier, or phase product.

Lines 136–158 prove the previously pending coefficient bridge for every
cardinality-m subset, not merely the nonleading ones:
`normalizedErrorCoefficient(S)*b_S^(n+m)=rawTerm(S)/N`.
The proof first extracts Aplus!=0 from actual N!=0 and its exact
factorization. It then uses the raw/normalized coefficient-ratio identity
only at theta!=0. Q's power and the factor `2*i*U` have proven nonzero
denominators. Thus the hard normalization is a conclusion, not a new
hypothesis about arbitrary coefficients.

## Exact remainder and Lemma 3

1. `DeterminantRemainder.lean:14–55` proves that the two leading **index
   sets** are distinct and partitions all cardinality-m subsets into the
   two singletons and exactly `BoundaryNonleadingSubset m hm`. Distinctness
   is about indices, so it remains valid at pi even though the oscillatory
   root values coincide. The finite subtype contains no duplicated or
   omitted subsets.

2. Lines 57–76 apply the literal grouped determinant expansion, the proved
   leading sum, and the proved nonleading term identity. The result is
   `D/N=sin(F)+boundaryErrorExpression` on 0<theta<=pi. This is an equality
   about the earlier finite expression; the expression is not redefined as
   D/N-sin(F) to make the identity tautological. The theta=0 exclusion is
   necessary because the raw normalizer vanishes there.

3. Lines 78–102 show that the finite complex expression equals the complex
   embedding of its real part on 0<theta<=pi, using actual D/N reality.
   `manuscriptError` is then the real part of that already constructed
   expression. Its ordinary real local regularity is proved on all [0,pi],
   and its derivative is the real part of the complex expression's ordinary
   derivative. At zero this provides an extension; it does not assert the
   raw normalized-determinant identity there. The manuscript only needs
   real smooth E on (0,pi], so the stated scope is sufficient.

4. Lines 104–112 give the eigenvalue equivalence only for 0<theta<pi,
   correctly excluding the artificial determinant zero at pi. The left
   side uses the actual integral-defined Toeplitz matrix's sorted
   eigenvalue with `1<=j<=n`, including the largest eigenvalue at j=n.
   There is no zero-based/off-by-one reinterpretation or assumed spectral
   representation in these statements.

5. Lines 114–127 transfer the proved complex value and derivative bounds
   to the real error by `abs(re z)<=norm z`. The two positive constants
   are chosen before both n and theta. They depend only on m, and the
   inequalities include n=0 and both interval endpoints. The exponent is
   `-c*n*theta`, with derivative prefactor n+1, exactly (11). No decay
   hypothesis is added to the public theorem.

6. Lines 129–139 prove E(pi)=0 by the earlier actual boundary-column
   collision, the normalization identity, and the proved exact phase
   endpoint `F_n(pi)=(n+1)*pi`. They do not assume an eigenvalue at pi or
   prove E(pi)=0 by declaring the endpoint value separately. N(pi)!=0
   is already part of the identity's established domain.

7. Lines 141–174 prove (12) by an ordinary mean-value estimate on the
   convex interval [theta,pi]. For t in that interval and theta>=pi/2,
   the sign `-c*n<=0` gives
   `exp(-c*n*t)<=exp(-c*n*pi/2)`. Multiplication uses the nonnegative
   factor C(n+1), and the interval length is pi-theta>=0. At theta=pi
   the right side is exactly zero; at n=0 the same argument remains
   valid. The constants are the ones supplied by the earlier exponential
   bound, so there is no hidden dependence on theta, n, or a subdivision.

## Independence and proof boundary

This report independently approves the two new assembly modules. It does
not serve as independent proof review of this reviewer's own imported
`PhaseProduct.lean`, `BoundaryErrorBounds.lean`, or earlier root-construction
sources. In particular, `BoundaryErrorBounds.lean` has source SHA256
`b6b6d491b44d1992c1903fd6dcc82d726914f7d2b23866ae1b65f04d0370132e`;
its bound statements were checked here as the exact interfaces being used,
but another reviewer must cover its internal proof for a blanket claim of
independent review of the whole Lemma 3 dependency chain.

The raw ratio/coefficient files were separately independently reviewed:
`NormalizedQuotient.lean` SHA256
`64b0c557994407c92cc1247d11d2701b2b3435acb966c9dabf95da9ddcb3863c`,
`NormalizedErrorCoefficient.lean` SHA256
`196098a5618651861b2d92ff8ce145b2e7425092241b97ed908a07b2bb85c52d`.
See `reviews/normalized-quotient-error-coefficient-review.md`. The prior
leading-coefficient and normalizer/conjugation reports cover the other
new algebraic dependencies within their expressly stated scopes.

Neither reviewed source contains a custom axiom, unresolved proof hole,
unsafe declaration, or native evaluation shortcut. The results use symbolic
finite sums, exact algebra, actual regularity, and the standard mean-value
theorem. No numerical certificate or enumeration is involved. They do not
prove later phase-root indexing, the all-orders implicit Taylor expansion,
the inverse-kernel limit, or the complete MF-21 Target. No completed
original-target count changes. The checks described here are actual local
Lean runs and independent source reviews; GitHub Comparator remains unrun.
