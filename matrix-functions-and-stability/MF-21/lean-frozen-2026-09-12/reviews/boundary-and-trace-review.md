# Independent boundary and trace review

Verdict: **APPROVE**, limited to the concrete algebraic identities in
BoundaryExpansion.lean and the scalar integral statements in TraceIntegral.lean.
This is not approval of Target, a trace limit, a spectral equivalence, or an
unrun Comparator check.

Reviewer: /root/mf21_restart_lean_audit, 20 September 2026. I did not write or
edit either reviewed Lean module. I did write BulkDecay, FourierStencil, and
FourierLaurent; those modules are explicitly excluded from this independent
proof review. I launched no compiler. Review follows the pinned
/Users/georgestepaniants/Research/project/lean-verification/REFEREE_STANDARDS.md,
SHA-256 e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1.

## Exact reviewed sources

All paths below are relative to the MF21-restart directory. These bytes were
read and hashed directly; the two proof-source hashes were rechecked after
the review.

| Path | SHA-256 |
| --- | --- |
| MF21Restart/BoundaryExpansion.lean | bc873ac5a5cb569d3dda0bc3b6ecf623e09d326f0d82cd613fdc3149c24a3979 |
| MF21Restart/TraceIntegral.lean | 373a63996684afa4d4424dc9fa46742d88163ae8fe1626815a7962d32e8f62fd |
| BOUNDARY_STATEMENTS.md | f9fc981a7484b340883f9b7e22358f9a3ea92d76f7754a418532f534bb1d1d97 |
| TRACE_STATEMENTS.md | 4d520573fb8783481137d912e809dc9ce28c6aa30b47139201b7f57986def89e |
| TRACE_SUBSTITUTION_NOTES.md | 8bf1b2d4b58273ddad93a5b550c2649697165ec12c9e78859c06f70ee19c9c29 |
| original-proof/solution.md | 6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa |
| MF21Restart/Definitions.lean | 35a74047a81a9b7526e9bf039880ca8f07ae33314e2b5b960ab254e02fca4b51 |
| evidence/logs/boundary-expansion-07.log | d76997439433a1e7ee8411a5503ab2b4c9c672ebeee95b0f06afb897819d53c1 |
| evidence/logs/trace-integral-02.log | 1fc1c7f198f174cd0d61e04b0a93279f03b886721741843155b711db0e90e7fe |

## Boundary expansion: source fidelity and proof

1. BoundaryExpansion.lean:20–30 defines the exact matrix in manuscript
   solution.md:149–156, equation (13). Its upper row exponents are
   0 through m-1; its lower row exponents are n+m through n+2m-1.
   In particular, n+row in the lower branch is correct. The split proved
   at lines 37–46 factors out w(col)^(n+m), leaving row-m. Natural
   subtraction is used only in the lower branch, where row>=m.

2. Lines 51–81 use Mathlib's proved alternating multilinear determinant
   API after transposition, so the splitting is in columns. Lines 83–92
   apply this to the defined matrix and prove the concrete grouped sum.
   No coefficient recurrence, determinant identity, or array bound is
   assumed as a hypothesis. The generic column-split helper supplies a
   proved algebraic step, not a substitute for the concrete result.

3. The cardinality argument at lines 124–155 uses the actual convention
   in Mathlib Matrix.det_apply': the permutation term is M(σ(col),col).
   It therefore proves col in S iff σ(col) lies in the bottom rows,
   and correctly concludes S.image σ = bottomRows. It does not confuse
   this image with the image of bottom rows under σ. The concrete
   cardinality calculation at lines 94–119 then proves vanishing unless
   |S|=m, and lines 157–169 restrict the sum to exactly those subsets.

4. Lines 178–227 order the complement first and the selected subset last,
   with each block in inherited order. The block identity at lines
   231–253 is correct: Mathlib's vandermonde has entry v(i)^j, whereas
   the manuscript puts powers in rows, so the transposes are necessary.
   Lines 255–281 prove the resulting coefficient equals the actual
   permutation sign times the two Vandermonde determinants. The sign is
   defined by a concrete permutation, not an arbitrary existential
   choice. Its possible values are the two units of the integers; the
   final sign inversion is justified by the explicit two cases.

5. The product order in lines 263–265 is V(S-complement)V(S), whereas
   manuscript equation (14), lines 164–166, writes V(S)V(S-complement).
   This is equal in the commutative field of complex numbers. Mathlib's
   det_vandermonde identifies each displayed determinant with the
   inherited-order product of differences used in the manuscript.
   Together the cardinal grouped expansion and coefficient theorem
   supply precisely equation (14).

6. No distinctness, nonzero-root, or modulus assumption is needed for
   these polynomial identities. Arbitrary exterior roots are admitted.
   Degenerate or repeated roots merely cause the appropriate determinant
   factors to vanish. The empty case m=0 remains valid, as do n=0 and
   nonempty degenerate lists. For a sign check, m=1 and S={0} produce
   the split matrix [[0,1],[1,0]], coefficient -1, and the defined
   permutation sign -1.

These are substantive identities for the manuscript's exact boundary
matrix. They still do not prove that its determinant zeros are precisely
the Toeplitz eigenvalues, or construct the characteristic roots. The two
leading terms (15), normalizer (16), normalized estimates (17)–(18), root
indexing, and endpoint cancellation remain outside this module. The
statement document accurately discloses those omissions.

## Trace integral: source fidelity and proof

1. TraceIntegral.lean:60–69 copies the diagonal polynomial in manuscript
   solution.md:328–332, equation (28), with the correct powers 2m-1 and
   denominator (2m-1)((m-1)!)^2. Its exact value is the scalar integral
   equality in solution.md:338–342, equation (29). It does not replace
   any of those factors by an asymptotic equivalent.

2. The general polynomial integral at lines 21–57 specializes Mathlib's
   Gamma_mul_Gamma_eq_betaIntegral to s=p+1 and t=q+1. The needed real-part
   positivity is proved for every natural p,q. The index p+q+1 in the
   denominator factorial is correct, because s+t=p+q+2. Conversion from
   complex powers to natural powers and then to the real integral is
   an equality, not an assumed integration rule. The denominator's
   nonzero proof explicitly uses factorial_ne_zero.

3. Lines 67–69 substitute p=q=2m-1 and factor out the constant denominator.
   The hypothesis 1<=m makes the natural-subtraction index arithmetic
   valid. It is inhabited and genuinely needed for the claimed positive
   integral; it contains every original m>=3 case. Sanity checks m=1
   and m=2 give 1/6 and 1/420 respectively.

4. Lines 72–85 prove strict positivity from positive factorials and
   2m-1>0. Lines 88–96 provide the explicit rational quotient as the
   existential witness and prove its cast equals the same integral.
   They do not assume a rational trace or two incompatible limits.
   No Toeplitz trace, inverse, limit, or critical uniform bound occurs
   in their hypotheses.

5. The statements match TRACE_STATEMENTS.md exactly. This is the integral
   evaluation once the diagonal kernel formula is established. It does
   not prove the representation (27), its diagonal substitution and
   reflection, the inverse-kernel limit (26), passage from that limit to
   matrix traces, dominated convergence in (31), or the final rationality
   contradiction. Both module comments and the statement lock state
   that limitation correctly.

## Trust, computation, and evidence

Static scans of both reviewed proof files found no sorry, admit, custom
axiom declaration, or unsafe shortcut. Their proof dependencies are
Mathlib results; neither imports the legacy project or Challenge. The
determinant arguments are symbolic for arbitrary m,n, not finite-size
enumeration. The integral proof uses a library theorem rather than
numerical certification, which is appropriate for an exact factorial
identity.

I independently inspected the two hashed local logs above. Each contains
four reported public theorems with exactly propext, Classical.choice, and
Quot.sound; neither contains an error or sorryAx report. The coordinator
explicitly reports boundary-expansion-07 exited 0. I did not launch those
processes, and these standalone logs are not a new complete-project run
record or a GitHub Comparator result. They must be retained alongside the
coordinator's final source-matched execution record. The new results have
not been approved here as Comparator contracts.

## Nonblocking documentation and integration observations

TRACE_SUBSTITUTION_NOTES.md correctly labels its substitution route as
unproved guidance. Its mathematical substitution and endpoints are
correct on 0<x<=1. One API name in the notes needs correction before use:
the pinned Mathlib theorem at Integrals/Basic.lean:173 is the global
integral_pow, not intervalIntegral.integral_pow; that file ends the
intervalIntegral namespace at line 109. This does not affect the reviewed
TraceIntegral source, which never uses that name.

For future exact Comparator contracts, the boundaryMatrix and
boundaryCoefficient definitions presently reside with their proofs in
BoundaryExpansion.lean. Put any definitions appearing in contract types
in a shared trusted definition module before configuring those contracts;
do not import this proof module into Challenge merely to obtain them.
This is a remaining integration step, not a defect in the standalone
algebraic identities reviewed here.

No complete original MF-21 target is proved by these modules, and this
review authorizes no increase in either completed-problem count.
