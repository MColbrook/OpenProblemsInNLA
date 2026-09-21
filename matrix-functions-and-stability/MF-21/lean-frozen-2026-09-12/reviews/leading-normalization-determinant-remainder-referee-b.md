# Referee B: leading normalization and determinant remainder

Verdict: **APPROVE**, for the six printed declarations in
`LeadingNormalization.lean` and nine in `DeterminantRemainder.lean`.
This is the independent manuscript agent's review of coordinator-authored
code. The reviewer ran no compiler and edited neither reviewed module.
The reviewer authored upstream `LeadingBoundaryCoefficients.lean` and
`LeadingBoundaryIndices.lean`; independent review of those dependencies
is explicitly outside this report.

This artifact preserves the scope and findings of this referee's earlier
review after two referees used the same report filename. The earlier
report's recorded hash was
`025489d0257ecbb19d1ec7a2736149c77208b044de9a86e790111ee45b6ecf73`.
The present text is a recreated report with its own hash, not a claim to
recover that earlier file byte for byte. Referee A's artifact is separate.

## Frozen sources

| Item | SHA-256 |
| --- | --- |
| `MF21Restart/LeadingNormalization.lean` | `74e5df08f291842541efcc6c92ca718121066d15a047daf213303bc4a8571de3` |
| `LEADING_NORMALIZATION_STATEMENTS.md` | `e6f878d869119c2a1eac5e5fbfdcfb7c59dcbc472f919be100371dce78f7c4af` |
| `MF21Restart/DeterminantRemainder.lean` | `3ff379de253810a3edaf355a243e26981c46d0052ca636aac5ace9b82bb6f318` |
| `DETERMINANT_REMAINDER_STATEMENTS.md` | `3f0e4ab188aed679b624d29fb439ae2f2f508fdabddfcbe19ef61ebf5c17d242` |
| `MF21Restart/BoundaryNormalizer.lean` | `7309e2650c79b925f4f4bb158b2b4fc435def898012e399d6b20d83579e8d3b6` |
| Imported `MF21Restart/LeadingBoundaryCoefficients.lean` | `f048a547bf8493c0355996d766e69562be5454bd0545ed4cb875e7dd957b7ab0` |
| Imported `MF21Restart/PhaseProduct.lean` | `1a4e719778fff8ed729c9bb6cc5f7615cf5d2aa0696b8df302c107afd64afeb1` |
| Imported `MF21Restart/BoundaryErrorBounds.lean` | `b6b6d491b44d1992c1903fd6dcc82d726914f7d2b23866ae1b65f04d0370132e` |

The unchanged manuscript hash is
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`;
the pinned referee rubric hash is
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Mathematical and statement checks

`boundaryPhaseMultiplier_factor` (`LeadingNormalization.lean:16`)
proves `U=z^(m-1)*exp(2*i*psi)`. The helper at line 25 multiplies
`conj(f)^2` by `f/conj(f)` and obtains `normSq(f)`, with the needed
nonzero denominator proved. Psi remains the sum of individual arguments;
no equality to the principal argument of the whole product is used.

`manuscriptNormalizer_eq_leading` (line 38) has the exact normalization
`N=Aplus*(2*i*U)*Q^(n+m)` and therefore
`N=(-2*i)*V(R)*V(O)*Q^(n+m+1)*normSq(f)`. It keeps the inherited minus
sign of Aplus, cancels only nonzero unit-root powers, and matches
manuscript (16), lines 184–189. The extra power of Q is present.

`boundaryCoefficient_leading_phase_relation` (line 62) has
`Aminus=-Aplus*U^2`. `leading_phase_quotient` (line 79) gives
`z^(n+m)/U=exp(i*((n+1)*theta-2*psi))=exp(i*F)`, with `1<=m`
justifying the natural subtraction cast. The two leading terms at
line 90 consequently give `N*sin(F)` through
`exp(iF)-exp(-iF)=2*i*sin(F)`. No phase shift or sign is chosen after
the calculation.

`normalizedErrorTerm_eq_raw_quotient` (line 136) proves the actual
cardinality-m term quotient in (18). The common zero-power cancellation
is used only for nonzero theta. The plus coefficient's nonvanishing is
derived from actual normalizer nonvanishing and the already-proved
identity, not from the target quotient. All identities retain
`m>=2` and `0<theta<=pi`; none divides at zero or assumes full-list
distinctness at pi.

`boundaryLeadingSubsets_ne` (`DeterminantRemainder.lean:14`) distinguishes
indices even when root values coincide at pi. The helper at line 28
removes exactly the two distinct leading subsets from the cardinality-m
power set and identifies the remainder subtype. The decomposition at
line 57 therefore comes from the actual finite Laplace expansion and
the exact leading and remaining quotients. The pre-existing finite error
expression is not redefined as the desired residual.

`boundaryErrorExpression_real` (line 78) subtracts the real sine from
the proved real normalized determinant. The real function at line 86
is its real part, and lines 89–102 derive ordinary local regularity
and its derivative through the real continuous-linear map `reCLM`.
The embedding equality is proved on `0<theta<=pi`; regularity and the
estimates hold on the closed interval. The eigenvalue criterion at
line 104 correctly restricts theta to `(0,pi)`, excluding the artificial
determinant root at pi. Taking real parts alone is not used as an
unjustified converse: reality was established first.

The constants in `manuscriptError_exp_bounds` (line 114) are chosen
before n and theta and preserve both exact factors in (11). Real
absolute values and derivative absolute values are bounded by the
corresponding complex norms. `manuscriptError_pi` (line 129) follows
from the actual colliding columns, the exact decomposition, and
`F(pi)=(n+1)*pi`; it is not assumed.

The endpoint estimate at line 141 uses the actual derivative throughout
`[theta,pi]`, the norm mean-value theorem, and endpoint zero. Since
`-c*n<=0` and `t>=pi/2`, the exponential comparison is correctly
`exp(-c*n*t)<=exp(-c*n*pi/2)`. It yields exactly
`C*(n+1)*(pi-theta)*exp(-c*n*pi/2)`, as in manuscript (12) and line 215.
The proof includes n=0 and theta=pi and does not divide by `pi-theta`.
No new estimate, spectral assertion, or numerical certificate is assumed.

No material issue was found. Unreachable trailing `ring` tactics and
an unused simp argument are optional polish only.

## Independently inspected local evidence

Both records state exit code zero and unchanged source; the reviewer
recomputed and matched source, log and output hashes. Both commands were
`lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/MODULE.olean MF21Restart/MODULE.lean`
with `LEAN_NUM_THREADS=1`.

| Evidence | SHA-256 |
| --- | --- |
| `leading-normalization-02.json` | `7bae8b67be3e48a3a8df326a9cfc31b8d9b9c6e7587efc5006e0f8f4b45c4c3f` |
| `leading-normalization-02.log` | `fe8b6a7d3546c92cfab7a36af13cc2d26d651703ca3fd3fadfe05e41cba44ea3` |
| `LeadingNormalization.olean` | `31e737cdee73c9b535f3194f6856f8f89432bfa8e5b9793f48b6ade8a28f42d6` |
| `determinant-remainder-02.json` | `4eaef2900fee304fbd2361701e57b4706c9a0220f2d295443f06a527f50c0463` |
| `determinant-remainder-02.log` | `f0a52c88cd30086f80bff8698ee346eccf03c148304f0cfa095e1bc090b08809` |
| `DeterminantRemainder.olean` | `8dfed6a9442c2890f1b925bd34e144e4d5e8b2a84946a9751b7475c9d4e3f5c6` |

The six plus nine printed declarations list only `propext`,
`Classical.choice`, and `Quot.sound`. These are actual coordinator local
runs, not runs by this reviewer. No GitHub Comparator, Linux sandbox,
eigenvalue-indexing theorem, or full MF-21 Target is claimed. Separate
independent reviews of `PhaseProduct` and `BoundaryErrorBounds` are
recorded in this referee's distinct reports.
