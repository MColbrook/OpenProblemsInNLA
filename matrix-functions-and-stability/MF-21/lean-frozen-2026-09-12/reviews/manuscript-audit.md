# Independent MF-21 mathematical audit, 20 September 2026

Reviewed source: /private/tmp/mf21-solution.md, identical in SHA-256 to
matrix-functions-and-stability/MF-21/solution.md at commit
eb37bc17a462177f57efa270e9a9f9b17e9d88e2.

SHA-256: 6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa

Scope: direct mathematical review of Sections 2–5, with special attention to
the determinant normalization, eigenvalue indexing, uniform expansions,
fixed-index limit, and trace obstruction. I read the local AGENTS.md. I did
not read or rely on previous agents' reviews, and did not run Lean,
Comparator, or numerical eigenvalue experiments. No manuscript or Lean
source was edited. Line numbers below refer to the reviewed source.

**Finding:** I found no false mathematical step in Sections 2–5. The
normalization, downward indexing, and fixed-index limit can be derived as
written. This is an informal mathematical audit, not a formal-verification
claim. The substantial dependencies listed below still have to be proved
for the concrete Toeplitz matrices or supplied by matching proved theorems.

## 1. Stable roots and the phase, lines 68–110

For theta in (0,pi], set s=2 sin(theta/2)>0. The characteristic equations
are 2-r-r^(-1)=omega_l s^2. A unit-circle root would make the left-hand side
real and nonnegative, whereas omega_l s^2 is either nonreal or negative
for 1<=l<=m-1. Since the two roots have product 1, precisely one is stable.
They cannot coincide: a double root requires the right-hand side to be
0 or 4. Both alternatives are excluded on this interval.

The local square-root branch in (8) is correct. If
kappa_l=exp(i(pi*l/m-pi/2)), then kappa_l^2=-omega_l and Re(kappa_l)>0.
Expanding 2-r-r^(-1) at r=1 gives
-(r-1)^2+O((r-1)^3), hence the stable branch is
r_l=1-kappa_l theta+O(theta^2).
One explicit branch construction is

    r_l(theta) =
      (sqrt(1-omega_l sin(theta/2)^2)
       - kappa_l sin(theta/2))^2.

The square root is chosen with positive real part. Its argument has
strictly positive real part on [0,pi], because Re(omega_l)<1. This gives
a smooth nonvanishing branch; stability follows near zero and then by
the absence of a unit-circle crossing.

The exponential bound (6) follows by extending
-log|r_l(theta)|/theta continuously to zero, where its value is
Re(kappa_l)>0, and taking a positive minimum over the compact interval
and the finite root list.

For each phase factor,

    (1-r_l(theta)exp(-i theta))/theta -> kappa_l+i
      = 2 sin(pi*l/(2m)) exp(i*pi*l/(2m)).

This verifies the argument limit and smooth extension in lines 103–110.
Conjugation sends l to m-l. At pi, each factor is 1+r_l, so paired
principal arguments cancel, and any unpaired real factor is positive.
Thus all four endpoint values in (7) are correct.

**Formalization traps, not manuscript errors:**

* The extended phase at zero is not the literal argument of the zero
  factors. In Lean, assigning arg(0)=0 and then using the same expression
  at theta=0 would give the wrong endpoint. The smooth extension has to
  be constructed.
* psi is the sum of the individual principal arguments; it is not in
  general the principal argument of their product f. For m=6, psi tends
  to 5pi/4, while the principal argument of f tends to -3pi/4. Replacing
  the sum by arg(f) changes the phase by 4pi after multiplication by 2
  and breaks the indexing. The identity f=|f|exp(i psi) in line 173 is
  valid without asserting psi=arg(f).

## 2. Boundary determinant and normalization, lines 142–215

The ghost indices are 1-m,...,0 and n+1,...,n+m. Shifting all indices by
m-1 produces exactly the row exponents 0,...,m-1 and
n+m,...,n+2m-1 in (13). In particular, the exponent n+m in (14) is correct.
The recurrence has nonzero leading and trailing coefficients. Distinct
characteristic roots therefore form a basis of its solution space.
Restriction to the interior identifies the boundary kernel with the
finite-matrix eigenvector space; injectivity follows from 2m consecutive
zeros, and surjectivity follows by recurrence extension of the eigenvector
and its prescribed ghost zeros.

Write L=m-1, R=(r_l), O=(q_l), z=exp(i theta).
Conjugate pairing gives Q=product(q_l)>0. If there is an unpaired root,
omega=-1 and its stable and exterior roots are positive real numbers.
With f=product(1-r_l z^(-1)), conjugate pairing also gives

    conjugate(f) = product(1-r_l z).

For the two leading subsets, direct multiplication gives

    V(z,O)V(R,z^(-1))
      = V(R)V(O) Q z^(-L) conjugate(f)^2,
    V(z^(-1),O)V(R,z)
      = V(R)V(O) Q z^(L) f^2.

Their Laplace signs differ because their selected column index sums
differ by one. Multiplication by (Qz)^(n+m) and
(Qz^(-1))^(n+m), respectively, therefore gives

    sigma V(R)V(O) Q^(n+m+1) |f|^2
      * (exp(i((n+1)theta-2psi))
         - exp(-i((n+1)theta-2psi))).

This is exactly (16). Both the phase sign and the n+1 exponent are
correct. There is no missing root product, power of z, or factor of 2i.

The denominator of each a_S has zero order

    2*binom(m-1,2) + 2*(m-1) = m(m-1)

at zero. Each numerator has zero order
2*binom(m,2)=m(m-1). All leading coefficients are nonzero: the
root slopes -kappa_l, +kappa_l, i, -i are distinct. Thus the quotient
does extend smoothly with bounded first derivative as stated in line
211. At pi, V(R), V(O), Q, and f remain nonzero. Only the oscillatory
columns coincide; this causes numerator zeros, not a denominator zero.

For every other subset, omitting an exterior root contributes its
stable reciprocal to the normalized modulus; adding an interior root
contributes another stable modulus. The case distinction in line 200
therefore proves (17). Since each b_S is smooth and nonzero on the
compact interval, its logarithmic derivative is bounded. Termwise
differentiation in the finite sum (18) yields both bounds in (11).

Conjugation permutes R and O with the same sign and exchanges the two
oscillatory columns. Hence D_n and the normalizer are purely imaginary
on the real interval, and their ratio is real. At pi, the coincident
columns force D_n=0; the nonzero normalizer and sin((n+1)pi)=0 then
force E_n(pi)=0. Integrating the derivative estimate over [theta,pi]
proves (12). No determinant-eigenvalue equivalence at pi is used.

**Formalization dependency:** a_S at zero must be defined by its
cancelled smooth expression or limiting value. The raw quotient
evaluates to 0/0 there and does not give the claimed extension.
Likewise, the determinant's nonzero normalizer is asserted for
0<theta<=pi, not at zero.

## 3. Root indexing and interlacing, lines 219–278

The quadratic-form argument gives strict spectral containment in
(0,4^m), and g is strictly increasing on (0,pi). Consequently the
matrix has exactly n eigenangles counted with multiplicity.

For large n, bounded eta' gives (20). Bounded eta also gives a uniform
lower bound on n theta in the region F_n>=Jpi-pi/4. Choosing the fixed
integer J sufficiently large makes both perturbations small there,
independently of n. Each I_(n,k), J<=k<=n, lies strictly inside
(0,pi), and (20) makes it an actual nonempty interval.

On I_(n,k), the derivative of sin(F_n) has constant sign and magnitude
at least (n+2)/(2sqrt(2)); the bound on E_n' preserves its sign.
Endpoint sign changes therefore give exactly one simple determinant
zero. If the boundary matrix had nullity at least two, every cofactor
would vanish and the derivative of its determinant would be zero.
The kernel identification and symmetry of A_n then give a simple
matrix eigenvalue. This argument does not assume that the analytic
multiplicity of every determinant zero equals eigenvalue multiplicity.

The sine is uniformly separated from zero in every intervening gap.
In the last half-band adjacent to pi, the mean value bounds give

    |sin F_n(theta)| >= c(n+2)(pi-theta),

whereas (12) is at most
C(n+1)(pi-theta)exp(-cnpi/2). For large n, the latter is strictly
smaller at every theta<pi. Thus pi is an artificial determinant zero
and produces no extra eigenangle.

This identifies exactly n-J+1 simple eigenangles in the upper part,
with none above or between them. There are exactly n eigenangles in
total, so counting downward identifies the root in I_(n,k) with the
k-th eigenangle. This indexing is valid without determining the
individual low-angle roots or invoking a separate oscillation theorem.

Applying the lower derivative bound for F_n to its exact root jpi
proves (19). That exact root is the same implicit solution Y, because
F_n(y)=jpi is equivalent to y=x_(n,j)+h eta(y).

The circulant argument is also correct. With N=n+2m, a wraparound
Fourier coefficient cannot enter the leading n by n block: a
wraparound distance is at least N-(n-1)=2m+1>m. Symmetry and monotonicity
of g on [0,pi] give the sorted eigenvalue formula with floor(j/2),
for both odd and even N. Repeated principal-submatrix interlacing gives
(21). For integer j>=2, floor(j/2)>=j/3, so the final inequality
in (22) has the correct constant.

## 4. Uniform expansions and the highest coefficient, lines 282–308

A smooth extension to a neighborhood permits a uniform implicit
function theorem on the compact x interval. The derivative in Y is
1-h eta'(Y), uniformly separated from zero for small h. A single smooth
family Y and uniformly bounded derivatives therefore give the uniform
Taylor remainder (23), including p=2m.

At h=0, every term of the k-th h derivative contains g^(s)(x), s<=k,
times bounded smooth factors. The order-2m zero of g proves (24).
The mean value theorem and the angle bounds (19) give exactly
h^(2m) j^(2m-1) exp(-cj) in (25). For the fixed set j<J,
interlacing and coefficient vanishing give O(h^(2m)) directly.
This proves the stated all-index order 2m-1 estimate, and bounded
coefficients then give all lower orders.

For j>=(log(n+2))^2, the exponential-polynomial factor is O(h).
One can formalize this by eventual monotonicity of
t^(2m-1)exp(-ct) and then comparing
(log(1/h))^(4m-2)exp(-c(log(1/h))^2) with h.
The ceiling causes no problem because j is an integer. Thus (23)
at p=2m gives Part 2 as claimed.

There is no omitted d_(2m) term in Section 5. Under the assumed
all-index order-2m estimate, subtract (23) at p=2m from that estimate.
Both expressions contain the full sum from k=0 through k=2m.
This gives line 348:

    lambda_(n,j) = g(Y(pi*j*h,h)) + O(h^(2m+1)).

Let alpha=eta(0). Smoothness and the implicit equation give, for fixed j,

    Y(pi*j*h,h) -> 0,
    Y(pi*j*h,h)/h = pi*j + eta(Y(pi*j*h,h))
                    -> pi*j+alpha.

Since g(t)/t^(2m)->1, dividing line 348 by h^(2m) gives (30).
The division leaves an O(h) error. This is a consequence of the
contradictory all-index hypothesis, not an assertion that the actual
extreme eigenvalues have this limit unconditionally.

To expose the earlier omitted-term objection precisely, (24) and
Taylor expansion at x=0 imply

    d_k(0)=0 for k<2m,
    d_(2m)(0)=alpha^(2m).

Consequently a sum truncated at 2m-1 would instead have normalized
fixed-index limit
(pi*j+alpha)^(2m)-alpha^(2m). That is a different expression.
For m=3 and j=1, these two limits are 63pi^6 and 64pi^6, respectively.
The manuscript uses the latter, because it retains d_6. Adding or
subtracting an extra alpha^(2m) in (30) would introduce an error.

## 5. Trace obstruction, lines 312–380

Primary-source check: [Böttcher–Widom, arXiv:math/0412269](https://arxiv.org/pdf/math/0412269),
page 4, paragraph preceding (13), states precisely the essential-uniform
step-kernel limit used in manuscript (26) for b=1. Page 3 defines the
grid index with the required endpoint convention. Formula (5), page 2,
matches manuscript (27), including its region x+y>=1 and the central
reflection symmetry. Thus this citation supplies a genuine external
theorem, not merely an operator-norm convergence assertion. I checked
the extracted primary-source text; the web screenshot operation was
unavailable. I have not formalized that external theorem.

For the diagonal substitution in manuscript lines 328–331, setting
u=1-x/t gives

    (t-x)^(2m-2)t^(-2m) dt = x^(-1)u^(2m-2) du.

The limits are 0 and 1-x. Multiplication by the outside factor x^(2m)
gives exactly (28); reflection covers x<=1/2.

Essential-uniform convergence alone would not control an arbitrary
function's diagonal. The extra structure in line 335 is sufficient.
Each approximating kernel is constant on every grid square. For a
chosen diagonal point, approach it through points in the corresponding
square outside the exceptional measure-zero set. Kernel constancy and
continuity of G preserve the same error bound at the diagonal point.
This also works at grid boundaries by approaching through the cell
whose constant defines the boundary value.

The diagonal integral of the step kernel is exactly
n^(-2m) trace(A_n^(-1)). The replacement of n^(-2m) by
(n+2)^(-2m) multiplies this by (n/(n+2))^(2m)->1.
The beta integral of (28) is the rational number in (29).
These are valid deductions from (26).

For the second trace limit, define the j-th inverse-eigenvalue term as
zero when j>n. Inequality (22) gives, for j>=2,

    h^(2m)/lambda_(n,j)
      <= (3/4)^(2m) ((n+2m)/(n+2))^(2m) j^(-2m)
      <= (3m/4)^(2m) j^(-2m).

The j=1 term is eventually bounded by the positive limit (30).
Finitely many earlier n may be discarded or absorbed in the bound.
This gives a summable majorant for counting-measure dominated
convergence. The spectral identity
trace(A_n^(-1))=sum_j lambda_(n,j)^(-1) then proves (31).

Both parity formulas (32) and (33) have correct lower indices. In the
odd case m=2r+1, j+a starts at r+1. In the even case m=2r, it starts
at r+1/2, so removing l=0,...,r-1 from the positive half-integer sum
is correct. For all m>=3, the removed sum is a strictly positive
rational number. Euler's even-zeta identity makes the remaining
zeta/pi^(2m) factor rational.

If u-v/pi^(2m) were rational with rational u,v and v>0, then
pi^(2m) would be rational; pi would then be algebraic. This contradicts
transcendence. The argument correctly uses transcendence, not only
irrationality of pi.

The unchanged target is consistent with this same-coefficient reading:
[BBGM Conjecture 8.4, page 26](https://arxiv.org/pdf/1710.05243).
The stronger assertion excluding every alternative continuous
coefficient family would additionally use uniqueness of regular
coefficients on dense bulk grids. That stronger uniqueness result is
not needed for the canonical statement's displayed quantifiers or for
the manuscript's stated construction.

## 6. Genuine proof obligations for full formalization

The following are substantive obligations, not counterexamples to the
mathematics:

1. Connect the concrete Fourier-defined Toeplitz matrix to the
   order-2m recurrence and boundary determinant, including equal
   kernel dimensions.
2. Construct the stable roots and the correct smoothly extended phase;
   prove decay, nonvanishing, conjugate pairing, and endpoint values.
3. Prove the exact Laplace normalization, smooth cancellation at zero,
   real error term, and both error bounds, including E_n(pi)=0.
4. Establish the ordered spectral interpretation of the bulk roots,
   simplicity, endpoint exclusion, and the exact index k=j.
5. Prove the concrete circulant embedding and interlacing estimates.
6. Construct one uniform smooth implicit family Y and its coefficient
   functions; prove the uniform Taylor remainder and coefficient jets.
7. Derive the all-index and logarithmic-cutoff estimates from those
   concrete spectral facts.
8. Prove or import a matching proved version of the inverse-kernel
   theorem, or a proved concrete trace-limit theorem sufficient for
   (29). Merely assuming a rational limit for an abstract array does
   not formally verify its application to this Toeplitz matrix.
9. Under the order-2m all-index contradiction hypothesis, prove the
   full g(Y) fixed-index limit, retaining the highest coefficient.
10. Prove the inverse-eigenvalue domination, counting-measure limit,
    zeta identities, and rational/transcendental contradiction for
    those same eigenvalues.

A theorem that takes the determinant estimates, eigenvalue indexing,
Taylor approximation, or trace limit as unproved hypotheses can be a
useful component, but cannot by itself be reported as a full Lean
verification of this manuscript. Conversely, the absence of those
formal proofs is not evidence that the corresponding manuscript steps
are false. No completed Lean verification or new mathematical
resolution is claimed by this report.

## 7. Audit provenance

The source identity was checked with these actual shell commands:

    git show eb37bc17:matrix-functions-and-stability/MF-21/solution.md | shasum -a 256
    shasum -a 256 /private/tmp/mf21-solution.md
    git rev-parse eb37bc17

Both SHA-256 commands returned the hash recorded above. The resolved
commit is also recorded above. The source was read with
nl -ba /private/tmp/mf21-solution.md; local instructions were read with
cat AGENTS.md in the repository root.

External source checks used web.open on the two arXiv PDF URLs linked
above and web.find for Conjecture 8.4. Extracted text was available;
no successful rendered-page inspection is claimed. An initial attempt
to fetch BBGM HTML returned a cache miss, followed by a successful PDF
text fetch. BW screenshot requests were unavailable, as noted above.

Local Lean commands: none. Local Lean logs or successful output hashes:
none. GitHub Comparator/kernel/sandbox runs: none. Run IDs: none.
Reviewer scope is mathematical source analysis of Sections 2–5;
there is no independent review of a completed Lean implementation here.

## 8. Pinned rubric and preliminary statement snapshot

I read /Users/georgestepaniants/Research/project/lean-verification/REFEREE_STANDARDS.md,
SHA-256 e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1.
Its source-fidelity and explicit-trust-gap standards are applicable to
this audit. Its final proof, Comparator, and implementation-review lanes
are not completed by this report.

Scoped mathematical source verdict: **APPROVE** — no material
mathematical issue found in the reviewed Sections 2–5. This verdict is
not approval of a completed Lean proof or permission to mark the
formalization complete.

At the coordinator's request, I also read the current restart statement
snapshot without running a compiler:

* MF21Restart/Definitions.lean, SHA-256
  35a74047a81a9b7526e9bf039880ca8f07ae33314e2b5b960ab254e02fca4b51.
* STATEMENTS.md, SHA-256
  6709fd19a3765c83ce16986780963e1f22ae49472b5ea7f013e968f37ab27691.

These files are under
/Users/georgestepaniants/Research/OpenProblemsInNLA/lean-verification/MF21-restart.
This is a limited source-fidelity observation, not a proof review.

MF21Restart.Target (Definitions.lean, lines 75–80) correctly uses one
coefficient family for all three canonical conclusions, quantifies over
every m>=3, and takes the negation of the same all-index order-2m bound.
The published index range in eigenvalue (lines 44–49) includes j=n and
maps to Fin n index j-1. No off-by-one error was found. Values outside
the valid index range are not used by the target.

The cosine Fourier coefficient at lines 20–22 has the correct real
normalization. Its equality to the original complex integral is a real
proof obligation, clearly acknowledged in the file and STATEMENTS.md.
The extra lower bound 1<=j in BulkBound is redundant for the original
cutoff but its equivalence should be proved as already recorded in
STATEMENTS.md, lines 12–15.

The target requests continuous coefficients, matching the canonical
problem. The manuscript's Theorem 1, line 21, additionally asserts
C-infinity regularity. A claim of verification of the full manuscript
must establish the stronger smooth coefficient construction and its
connection to this target, not stop with continuity alone.

STATEMENTS.md, lines 49–57, correctly presents the fixed-index analytic
lemma as conditional on the implicit relation, continuity, and the
required approximation error. It explicitly says this lemma alone
does not establish those hypotheses for the Toeplitz eigenvalues.
That is the proper scope for this intermediate result.
