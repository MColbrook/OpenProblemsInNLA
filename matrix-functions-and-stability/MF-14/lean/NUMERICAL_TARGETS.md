# MF14 degree44: exact numerical and symbolic targets before proof development

Status: proposed statements; no Lean proof or compiler run. Two independent
statement approvals and a successful exact-header elaboration are required
before substantive implementation. This is a separate route to the original
negative answer, not an amendment to the frozen degree47 gate.

## Exact source and full targets

The primary source is Marcus Webb's degree44 proof at upstream commit
e7519c46fd249a6a033bfe5d11c66bf47f7f8885, Section 2 and Section 3. All scalar
parameters are complex. Numeric certificates below are exact integer or
symbolic polynomial equalities; no floating-point diagnostic is a premise.

The original ambient definition remains Fin129→ℂ, and the final targets are
NLA.MF14.CoversDegree 44 and ¬ IsGreatest NLA.MF14.coveredDegrees 42. These are
unconditional. The exact maximum47 is not a target of this proposed package.

## N1: symbolic fourth-product minor

The 12 affine directions are fixed by fourthPolynomial, the exact rows are
[0,1,2,3,4,5,6,8,9,10,12,16], and fourthDerivativeColumns fixes column order.
For every alpha,eta,gamma,s,lambda in ℂ, prove the actual derivative/table
identity and

  det(fourthJacobian) = (s^2)^5 *
    (lambda - eta - alpha*lambda*(gamma*s - s^2*lambda)).

The equality includes s=0 and all exceptional parameter values. The good-s
predicate used for the density step separately requires s≠0,
gamma*s−2*s²≠0, and this minor at lambda=eta+1 nonzero. Prove that these
conditions hold eventually as nonzero s approaches zero, for every fixed
alpha,eta,gamma. No input parameter is excluded from the final border lemma.

Computation plan: with a=s², b=gamma*s, c=b−a*lambda, subtract
(a*column8 + column6 + c*column7) from the R_s column (1-based column5).
Its remaining polynomial is (eta−lambda)X³−c*lambda X⁴. The selected matrix
has a 2×2 block [[alpha,eta−lambda],[1,−c*lambda]] plus scalar pivots
1,1,1,1,1,1,a,a,a,a². This proves the determinant without enumerating 12!
permutations. The projection onto the selected rows must independently be
bijective on the full productSpan; row rank is not a projection shortcut.

## N2: exact degeneration syzygy

Degeneration.lean copies five explicit scalar polynomials from the primary
symbolic certificate, without importing its verdict. They define E_s as a
linear combination of [X²R_s,Q²,QR_s,R_s²,XR_s]. Prove, for every complex
alpha,eta,gamma,s,

  E_s - lowPart6(E_s) = -C(s^4)*Z_s,

where Z_s is the displayed polynomial supported on coefficients11,...,16.
In particular coefficients7,...,10 on the left vanish exactly, and no
coefficient above16 exists. Prove

  Z_0 = X^12 + C(3*alpha - 4*gamma²)*X^11

and, for s≠0, Z_s belongs to the full productSpan. lowPart6 is explicitly an
algebraic helper justified by the span of 1,...,X6; it is not a free circuit
operation. Only these direct identities matter: proving that the five scalar
polynomials came from determinant cofactors is unnecessary.

## N3: exact 45-variable coefficient derivative

The exact parameter blocks, zero-based, are:

- alpha:0, beta:1;
- xi3,xi6,xi7,xi8,xi9,xi10,xi11:2,...,8;
- u:9,...,12; v:13,...,15; a:16,...,20; b:21,...,23;
- c:24,...,29; d:30,...,35; z:36,...,44.

The base point is1 precisely at indices0,22,32,34,35,44; it is0 elsewhere.
All 45 coefficient rows0,...,44 and all45 parameter columns are retained.
The compact integerDerivativeColumns definition gives the manuscript table
using q=X4+X3, r=X5, p=X12, f=X17, g=X22+X19,
h=g(g+q+p+f), b=r+X2, k=2g+q+p+f, l=kb+g.

Prove jacobianAt coefficientMap basePoint = (integerJacobian cast to ℂ).
This connects the actual derivative of the full displayed family to the
small integer data. The table is not assumed correct by definition.

## N4: small exact nonsingularity witness

The closed kernel obligation is

  ∃ B : Matrix (Fin45) (Fin45) (ZMod3), integerJacobianMod3 * B = 1.

The matrix to invert is already completely determined by N3's transparent
integer polynomial definitions. After statement approval, the published
inverse-mod3 data can instantiate B; every product entry must then be checked
inside Lean, in small independent partitions. No inverse table, checksum or
Python Boolean is an assumption. Determinant naturality over ℤ→ZMod3 and
ℤ→ℂ implies actual derivative nonsingularity. The published exact determinant
256 need not be formalized because nonzero is the consumed assertion.

A prior assessment's bounded Python check found all2025 modular products
correct and matched the table to the stored matrix. That is feasibility
information, not evidence of any Lean check. No large matrix arrays are
included or generated in this statement packet.

## Precision, runtime and trust

No interval precision/radius is introduced: this route uses exact integers,
finite-field arithmetic and symbolic polynomial identities. Pin LeanCert and
use kernel mode for all later numerical decisions/trust checks. Do not add
native_decide, custom axioms, opaque unverified data claims, or numerical
bounds as final hypotheses. Begin with the reusable density and 12-variable
interfaces; pilot small arithmetic partitions before batch generation.
Only root runs the serial local compiler, one thread and4096MiB. Final Linux
Comparator checks remain a later separate GitHub step. No run is claimed here.
