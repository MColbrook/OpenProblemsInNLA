# MF-21 restart: independent statement review

**Verdict: APPROVE for the mathematical semantics of the new target and one-based eigenvalue definitions.** This is a statement-design review, not approval of a completed proof, a compilation claim, or a Comparator result.

Date: 20 September 2026. Lane: source fidelity and correctness under the pinned [REFEREE_STANDARDS.md](/Users/georgestepaniants/Research/project/lean-verification/REFEREE_STANDARDS.md), SHA-256 e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1. No compiler was run by this reviewer. No shared source was edited.

Reviewed files:

| File | SHA-256 |
| --- | --- |
| MF21Restart/Definitions.lean | 35a74047a81a9b7526e9bf039880ca8f07ae33314e2b5b960ab254e02fca4b51 |
| STATEMENTS.md | 6709fd19a3765c83ce16986780963e1f22ae49472b5ea7f013e968f37ab27691 |
| Frozen original-proof/solution.md | 6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa |
| Unchanged canonical README | 1aac38ed3c7a83dfc3dddb4beeec26fcf117f23f5789b2a374c1332ba4cf359f |

Line references to Definitions.lean are to the exact 82-line reviewed version at that hash.

## Checks passed by inspection

- **Actual symbol:** line 18 uses exactly (2*sin(theta/2))^(2m), with natural exponent 2m.
- **Toeplitz offset:** lines 24–25 perform subtraction in the integers. This avoids accidental truncated natural subtraction and agrees with the original row-minus-column Fourier convention.
- **Ordered eigenvalue multiplicities:** lines 38–42 sort the full n-entry list obtained from the Hermitian spectral construction. No eigenvalue is dropped by converting the list to a multiset and sorting it.
- **One-based accessor:** lines 46–49 check 1<=j<=n before selecting Fin n index j-1. At j=1 this is the minimum; at j=n>=1 it is the maximum. n=0 has no admissible j. The totalized zero outside the range is not used by any target inequality. The in-range bridge at lines 51–53 matches that convention.
- **Mesh and expansion:** lines 55–61 use j*pi/(n+2) and terms k=0,...,p divided by (n+2)^k. All divisions are real; there is no natural-number quotient.
- **Lower orders:** lines 63–66 and 79 match the original positive-constant/eventual-n estimate for every natural p<=2m-1 and every 1<=j<=n. The constants are allowed to depend on m,d,p.
- **Critical bulk:** lines 68–71 use the exact ceil(log(n+2)^2) threshold, the critical truncation 2m, and denominator exponent 2m+1. There is no arbitrary existential threshold and no assumed exponential estimate.
- **Critical obstruction:** line 80 negates the uniform critical bound for the same coefficients d. Its quantifier direction matches the original no-D,N assertion.
- **Global quantifiers:** lines 75–80 quantify every natural m>=3 and choose d once per m, outside n and j. One common family supplies all orders, the bulk estimate, and the non-uniformity assertion.
- **Coefficient domain:** line 77 requires continuity only through index 2m on [0,pi], and line 78 requires d_0=symbol only there. Representing this finite family by a total natural-indexed family introduces no restriction on the target.
- **No proof hidden in a proposition definition:** Target is a definition of the conjecture, not an asserted theorem. The file does not smuggle its conclusion into an axiom, typeclass, or proof assumption.

## Required connecting lemmas before a complete faithfulness claim

These do not make the target definition mathematically incorrect. They remain explicit work needed before the formal declaration can be presented as a fully checked translation of the original complex-Fourier statement.

1. **Cosine coefficient equals the complex coefficient.** Lines 20–22 define the real cosine integral. Prove that its complex cast equals the normalized integral of symbol times exp(-i*k*theta). The imaginary integrand is odd because the real symbol is even. STATEMENTS.md lines 12–13 correctly mark this as an obligation. Preserve the integral limits, factor 1/(2*pi), and negative exponential sign in the bridge.

2. **The added positive-index bulk guard is redundant.** The original bulk formula does not separately repeat 1<=j. Definitions.lean line 70 does. For every n:Nat, n+2>1 gives log(n+2)>0, hence log(n+2)^2>0 and 1<=Nat.ceil(log(n+2)^2). Thus the two admissible index sets are identical. STATEMENTS.md lines 14–15 correctly mark the formal proof of this fact as pending.

No semantic weakening results from these choices once the elementary bridges are proved. No new material defect was found in Target, BulkBound, UniformBound, or eigenvalue.

## Review of the analytic statement selected before proof

STATEMENTS.md lines 49–57 describe a valid useful lemma:

- h_n tends to zero and is eventually positive;
- y_n tends to zero;
- eta is continuous at zero;
- y_n=b*h_n+h_n*eta(y_n) eventually.

Dividing by the eventually nonzero h_n yields y_n/h_n=b+eta(y_n), hence the claimed quotient limit. For the concrete symbol,

    2*sin(y_n/2)/h_n
      = (y_n/h_n)*sinc(y_n/2),

including y_n=0 using the standard sinc convention. Its limit is b+eta(0); taking power 2m gives the symbol-scaling limit. An eventual error bound C*h_n^(2m+1) becomes an error at most C*h_n after division by the positive h_n^(2m), which tends to zero.

The proposed statement is valid even when y_n vanishes along a subsequence; avoid introducing a gratuitous assumption y_n!=0 in the proof. m=0 also causes no contradiction, although the eventual MF-21 application has m>=3.

This module must retain the clear scope warning in lines 56–57: it does not itself prove that the Toeplitz eigenvalues satisfy the assumed error estimate. For the manuscript application, that estimate must be derived by combining the critical Taylor approximation with the hypothetical uniform critical remainder bound. Continuity of arbitrary coefficient functions alone is insufficient.

The obligations list in STATEMENTS.md lines 19–38 corrects the earlier manuscript mismatches: grouped normalized determinant terms, phase/index counting, small-index interlacing, the h^(2m)*j^(2m-1)*exp(-c*j) error only above J, a Taylor remainder without an exponential factor, and a spectral limit conditional on the assumed-for-contradiction uniform bound.

The complete original target and complete Lean-verification counts remain unchanged.
