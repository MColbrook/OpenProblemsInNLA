# Independent recurrence-basis review

Verdict: **APPROVE**, for the two general recurrence and Vandermonde results
actually stated. They do not yet prove the MF-21 characteristic-root or
boundary/eigenvalue bridge.

Reviewer: /root/mf21_restart_lean_audit, 20 September 2026. I neither wrote
nor edited RecurrenceBasis.lean and launched no compiler. This review
follows the pinned REFEREE_STANDARDS.md at
/Users/georgestepaniants/Research/project/lean-verification/REFEREE_STANDARDS.md,
SHA-256 e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1.
It excludes my own Fourier and bulk-decay modules.

## Source and evidence identity

Paths are relative to the MF21-restart directory.

| Path | SHA-256 |
| --- | --- |
| MF21Restart/RecurrenceBasis.lean | ef4a5d7bbbb5db6e849ec6dbbc9289bda98300d7e1a7f78e47c26fd61457454b |
| RECURRENCE_STATEMENTS.md | 2c8d11042e745e2b144af23f8b4d4f26dcb9537b30437947687d3905ba10abbc |
| evidence/logs/recurrence-basis-02.log | edf49029e02fa9da240beeff536690bf98162cf56a9aec78af4fb7265859c120 |
| original-proof/solution.md | 6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa |
| MF21Restart/Definitions.lean | 35a74047a81a9b7526e9bf039880ca8f07ae33314e2b5b960ab254e02fca4b51 |

The coordinator reports recurrence-basis-02 exited 0. I independently
read its hashed log: both public results report only propext,
Classical.choice, and Quot.sound, with no errors or sorryAx. This is
local Lean evidence, not a GitHub Comparator run. I did not independently
launch or observe the compiler process, and a final source-matched run
record remains the coordinator's evidence obligation.

## Statement fidelity

The source manuscript, solution.md:142–159, uses a basis of characteristic
root sequences to pass between its recurrence and finite boundary system.
The new theorem at RecurrenceBasis.lean:44–48 isolates the necessary
general fact without pretending that an arbitrary recurrence has already
been identified with the concrete Fourier stencil.

Mathlib's LinearRecurrence.IsSolution means

    u(n+d) = sum_i E.coeffs(i) * u(n+i),  i in Fin d,

and its characteristic polynomial is

    X^d - sum_i E.coeffs(i) * X^i.

Those conventions are explicit in the inspected pinned
Mathlib/Algebra/LinearRecurrence.lean:70 and :209. Thus the theorem concerns
a recurrence whose leading coefficient is normalized to 1. It correctly
requires exactly d distinct roots via w : Fin E.order -> Complex,
injectivity of w, and the individual characteristic-root equations.
It assumes neither an expansion of u nor the existence of its coefficient
vector. The conclusion proves both existence and uniqueness for every
natural index. The locked statement document describes exactly this scope.

The separate theorem at lines 79–82 concerns any d distinct nonzero
complex numbers and any coefficient vector. It proves that vanishing
on a block of d consecutive natural indices forces the coefficient
vector to be zero. A root-of-a-particular-polynomial hypothesis is
unnecessary for this Vandermonde conclusion and is appropriately absent.

## Proof inspection

1. Lines 21–40 first prove that the geometric combination is a solution.
   The proof invokes Mathlib's geom_sol_iff_root_charPoly on the given
   root equations and distributes and interchanges finite sums. It does
   not assume the key solution assertion as a hidden premise.

2. Lines 50–64 build the transposed Vandermonde matrix, prove its
   determinant nonzero from injectivity of w, and solve for the first d
   values by its nonsingular inverse. Using the transpose is correct:
   Mathlib.vandermonde(w)(i,j)=w(i)^j, so row k of the transpose evaluates
   the geometric combination at index k. Matrix.mul_nonsing_inv is used
   only with an explicit unit determinant proof; the totalized inverse
   is not used at a singular matrix.

3. Lines 65–69 apply Mathlib's proved recurrence uniqueness theorem,
   eq_iff_eqOn_range_order, to extend initial agreement to all indices.
   Lines 70–75 then prove uniqueness of the coefficient vector by the
   injectivity of multiplication by the same Vandermonde matrix. This
   is substantive reconstruction, not a restatement of a representation
   supplied as a hypothesis.

4. Lines 83–96 rewrite a zero block beginning at a as multiplication of
   the transposed Vandermonde matrix by the vector c(i)*w(i)^a.
   Nonsingularity forces that vector to vanish. Lines 97–99 cancel
   w(i)^a using the explicit nonzero-root hypothesis. That hypothesis
   is necessary for arbitrary starting a: with d=1, root w=0, c=1,
   and a=1, the observed block vanishes without c vanishing. The first
   basis theorem correctly omits this hypothesis, since a zero root
   still gives a valid initial-value solution on natural indices.

5. The zero-order case is valid. A Mathlib recurrence of order zero
   has only the zero solution, and its coefficient vector has domain
   Fin 0. The empty geometric sum is zero and the vector is unique.
   The second theorem similarly concludes equality of the unique
   empty vector. No positive-order or nonempty-root premise is hidden.

The proof reuses the existing recurrence solution criterion, uniqueness
API, Vandermonde determinant criterion, and nonsingular inverse API. The
relevant inspected Mathlib recurrence and Vandermonde modules provide
these ingredients but do not already expose the stated geometric
coefficient reconstruction. No finite root enumeration or numerical
certificate is used. Static inspection found no sorry, admit, custom
axiom declaration, unsafe shortcut, or import of the legacy project.

## Remaining application obligations

The new theorem is conditional on a normalized recurrence and a full list
of distinct characteristic roots. The MF-21 application must still:

- construct that recurrence from the actual Fourier coefficients, with
  its leading coefficient justified nonzero and all signs and index
  shifts correct;
- prove that the proposed 2m roots satisfy its characteristic polynomial,
  are pairwise distinct, and, where needed, are nonzero;
- map shifted natural sequence indices to the actual ghost values and
  finite Toeplitz matrix equation;
- prove the resulting kernel correspondence and nonzero-vector claims.

The manuscript restricts its eigenvalue criterion to 0<theta<pi at
solution.md:119–123. The injective-root theorem cannot be applied to a
coalescing endpoint root list without a different argument. The current
module makes no such endpoint claim.

Neither a spectral asymptotic nor Target is a hypothesis or conclusion
of these results. This review approves their stated general algebraic
scope and does not authorize a completed-original-problem count or any
unrun Comparator claim.
