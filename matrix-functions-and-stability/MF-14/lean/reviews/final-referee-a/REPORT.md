# MF14 final independent source review — APPROVE

Reviewer: `/root/nr04_mf14_final_referee_a`, an AI agent and nonauthor of this
formalization. Phase: final statement-fidelity, proof-correctness, and bounded
reuse/API/documentation review, 19 September 2026. I did not write or modify
any Lean proof, run Lean, run Comparator, or modify publication files. My only
writes are these review artifacts and an independent Python arithmetic audit.

**Verdict: APPROVE the frozen statement and proof source for the complete
unchanged original MF-14 target.** I found no blocking mathematical or source
correctness issue. This is source-review approval, not a Linux Comparator
result, a publication approval of all surrounding metadata, or a count change.
The formalized result is unconditional degree-44 coverage, which refutes the
original proposed equality 42. It does not establish the later stronger exact
maximum 47.

## Exact scope and identity

The reviewed packet is `.local-recovery-20260918/final-review-packets/MF14-v1`.
Its `REVIEW-SNAPSHOT.json` SHA-256 is
`e52fab5a7b58c3bc6fb2c2df1283d55c6e4352056689c900de936c12e2595436`.
I read all 87 Lean files, the unchanged canonical README, the complete retained
Marcus Webb degree-44 mathematical source, the numerical-target plan, the
statement freeze, build pins, Comparator contract, and local aggregate evidence.
I read the adapted review protocol pinned to Tau Ceti commit
`afb424eda89e8ac96d9eb69f6a88972055a4cd1b` and the workflow; their bytes are the
same as the protocol/workflow read for my preceding NR04 review. This is not an
official Tau Ceti review or endorsement.

I independently recomputed all 101 registered file hashes, checked that the
Lean inventory contains precisely the 87 registered files, and found no
mismatch. All 25 Challenge headers have exactly one corresponding implemented
declaration and match it after whitespace normalization. The Challenge,
original MF14 definitions, degree-44 definitions, Family, Degeneration,
numerical targets, Comparator contract, and toolchain retain the hashes in the
preproof freeze. The manifest and audit JSON bind the individual files and
headers. My proof review did not rely on an author's PASS assertion or the
earlier reviewers' conclusions.

The historical upstream scope recorded in the packet is commit
`71563f17926cd826a892c2bba0e294894ee57a5c`; the degree-44 source itself is retained
byte-for-byte under its recorded hash. I performed no new upstream/fork/PR
novelty search. This is verification review of an existing mathematical
resolution, not a claim to a new resolution.

## Fidelity to the original question

`NLA/MF14/Definitions.lean` uses complex scalar coefficients and a chronological
circuit: each charged gate is the product of two elements of the complex span
of 1, X, and earlier products. Its final output is an arbitrary free linear
combination of these available polynomials. There is no hidden genericity,
invertibility, bounded-coefficient, or nonzero-parameter assumption in the
original output predicate. `canonical_gate_padding` proves the equivalence
with at most seven products, including zero products, by legal zero padding.

The original coefficient space is `Fin 129 → ℂ`, covering every coefficient
through the maximum circuit degree 128. `sevenProductClosure` is the common
zero set of every multivariate polynomial equation vanishing on the actual
circuit outputs. `degreePlane 44` includes every vector with all coefficients
above 44 zero, including the zero polynomial and all lower degrees.
`degree44_coverage` therefore asserts the required full inclusion in the
original Zariski closure. `original_equality_false` consumes membership of 44
in `coveredDegrees` and contradicts 44 ≤ 42. Its conclusion
`¬ IsGreatest coveredDegrees 42` answers the original equality question.

The newer degree-47 mathematics appearing later in the canonical README is
not silently substituted for that original target. Conversely, the proof does
not claim to formalize all of Webb's stronger intermediate arbitrary-P border
lemma: the frozen monic seven-coefficient family is exactly the subfamily
needed for this complete degree-44 negative answer. This restriction loses
neither a parameter needed for the 45-dimensional continuation nor an original
target quantifier.

## Proof path and substantive checks

**Legal shared circuits and complete coordinates.** The prefix and append
lemmas retain one common circuit for the entire intermediate tuple. The
three-product factorization uses the stated nonzero denominator and an exact
polynomial identity, then a free span correction. Appending the displayed
fourth product preserves all three earlier outputs simultaneously. Strong
induction on genuine prefixes proves the degree bound: four available
products have degree at most 16, so decoding the complete 68-coordinate tuple
recovers the original four polynomials exactly. No arbitrary truncation is
declared to be a circuit operation.

**Fourth-product density.** The fourth polynomial is the actual affine
12-parameter product-plus-span map. Its smoothness follows coefficientwise
from finite polynomial convolution. The first-jet helpers prove actual
coefficient derivatives and differentiability, and `fourth_jacobian_identity`
identifies the actual `fderiv` matrix in the standard basis with the compact
table. The exact determinant proof reduces the 12-by-12 matrix to small
blocks. It proves

`(s²)^5 * (λ − η − αλ(γs − s²λ))`

for every complex parameter value, including s = 0 and zero determinant
cases. It does not assume its nonsingularity. Separately, the chosen 12
coordinates are proved bijective on the full product span when s ≠ 0, through
the explicit basis-coordinate matrix and full-polynomial reconstruction.
Thus the 12 selected coefficients cannot conceal an unproved higher tail.

The generic density bridge uses Mathlib's inverse function theorem to place a
nonempty open neighborhood inside the map's range. A polynomial vanishing on
that range vanishes on a product of infinite coordinate sets and hence is
zero. The empty-dimensional case is retained. No unjustified global
surjectivity or global inverse is asserted. `fourth_product_joint_closure`
pulls back an arbitrary polynomial equation in all 68 joint coordinates
through the full span reconstruction, applies density, and evaluates at an
arbitrary member of the span. It proves simultaneous joint closure, not four
separate closure claims that might require incompatible circuits.

**The singular degeneration and all final parameters.**
`good_border_parameters_eventually` is proved for every α, η, γ. The γ = 0
branch is explicit; the factor then reduces to a nonzero multiple of s² on
the punctured neighborhood. At λ = η + 1 the remaining determinant factor
tends to 1. No genericity restriction survives into the border theorem.

The five syzygy coefficients are transparent scalar polynomials. The proof
expands the entire polynomial, verifies the cancellations at degrees 7–10,
and factors the high part exactly to establish
`E_s − lowPart6(E_s) = −C(s⁴) * Z_s` for all s. It proves the literal value
`Z_0 = X¹² + C(3α − 4γ²) * X¹¹`. Low-part subtraction is justified inside the
product span because it contains the required monomials; it is never treated
as a free circuit operation. Division by s⁴ occurs only with s ≠ 0.

The explicit triangular corrections construct the full monic border path.
Existence of a complex square root supplies γ for every coefficient of X¹¹;
η = β + α² gives the requested third limiting output. Coefficientwise
continuity applies to the whole 68-coordinate path. The joint vanishing hull
is closed in the usual complex topology, being an intersection of continuous
polynomial zero sets. The limit argument uses a nontrivial punctured complex
neighborhood. Helpers that accept a fourth-product closure hypothesis are
not the final result: `FinalClosure.lean` supplies the independently proved
`fourth_product_joint_closure`, giving unconditional
`monic_border_joint_closure`.

**Three continuation products and full final closure.** The continuation
appends exactly three legal products to one four-product prefix. The transfer
lemma pulls back every polynomial equation in all 129 output coordinates
through an explicitly coefficientwise polynomial map of the 68 input
coordinates. The generic decoded continuation has degree at most 96 and fits
the canonical ambient space. The limiting family has degree at most
`2 * (12 + 5 + 5) = 44`, and `family_degree_and_full_vector` proves equality
with its full zero-extended 45-coordinate vector. This proves the higher
coefficients vanish; it does not merely project them away.

**Actual 45-variable Jacobian and exact nonsingularity.** The parameter blocks
cover indices 0–44 without modular wrapping; `parameterIndex` carries the
necessary bound. The family first jet follows the actual three continuation
products and free output combination. All 45 whole-polynomial derivative
identities are proved and assembled, then coefficient extraction gives the
actual derivative matrix. The 45 column table matches and all 45 inverse-row
claims cover every entry. The finite arithmetic uses `decide +kernel`, not
native evaluation. The modular inverse is constructed and every product
entry verified. Determinant naturality from integers to `ZMod 3`, and the
injective integer cast into ℂ, give nonsingularity of the actual complex
derivative. No stored determinant or Python verdict is a Lean premise.

As a separate corroborating calculation, I wrote and ran exact integer dual
polynomial arithmetic directly through the displayed continuation at its
base point. It independently matched all 2,025 stored Jacobian entries,
verified all 2,025 products for the supplied inverse modulo 3, and computed
integer determinant 256 by fraction-free elimination. This Python audit is
not a Lean/kernel run and is not a substitute for the formal proof.

Finally, the coefficient map's polynomially dense range and the proven full
family-vector equality transfer arbitrary vanishing equations to every point
of the full degree-44 plane. There are no undischarged density, closure,
Jacobian, or degree-bound hypotheses in either final contract.

## Trust, reuse, API, and attribution

After removing comments and strings, an independent recursive source scan
found only the 25 intentional Challenge placeholders and no other `sorry`,
`admit`, custom `axiom`, unsafe declaration, native decision, external
implementation, or reduction-axiom escape. No proof module imports Challenge.
The aggregate audits report exactly `propext`, `Classical.choice`, and
`Quot.sound` for every one of the 25 contracts. Comparator permits exactly
those axioms and compares the isolated Challenge to Solution.

The pinned Lean version is v4.33.1, Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert commit
`621a43d7cf21f87872392a01e874f2f1dbddc926`. I inspected the actual pinned
Mathlib definitions/theorems for the strict-derivative open partial
homeomorphism, `MvPolynomial.funext_set` (including its dimension-zero case),
and the determinant/continuous-linear-equivalence interface. A bounded search
of the relevant Calculus, MvPolynomial, and topological polynomial modules
found no ready-made version of this complete density bridge. This is a
bounded reuse check, not an exhaustive Mathlib novelty claim. The
formalization reuses the existing IFT, polynomial extensionality, matrix,
span, differentiation, and topology APIs rather than re-proving those major
results. The custom coefficient/first-jet helpers are appropriately local to
this large explicit polynomial family. The small symbolic determinant and
partitioned modular witness avoid an unnecessary 45-by-45 symbolic determinant
formalization or floating-point certificate.

The source preserves Marcus Webb's mathematical authorship and University of
Manchester affiliation, prior mathematical source attribution, and the
formalization credit to George Stepaniants, Department of Computing and
Mathematical Sciences, California Institute of Technology, with Codex
assistance. The packet carries an Apache 2.0 license. I do not claim ownership
of either the mathematics or Lean code.

Two nonblocking documentation observations remain in the frozen historical
packet. Challenge and NUMERICAL_TARGETS retain preproof statements that no
implementation exists; the freeze explicitly identifies these as preserved
historical prose. The frozen Lake manifest's top-level project name is
`NLAPF03`, while the project is `NLAMF14Degree44`. I separately inspected the
publication copy supplied by root: its top-level name is corrected to
`NLAMF14Degree44`, dependency entries are unchanged, and all 87 Lean files
still match this frozen review byte-for-byte. These observations do not alter
the mathematical verdict; I made no source or publication edit.

## Mechanical evidence actually inspected and limits

The frozen local evidence is an actual macOS direct Lean run, not a Linux
Comparator run. Receipt `RECOVERY-087.json` records the aggregate
`MF14Degree44Solution.lean` from 07:49:48.789710 to 07:49:53.577446 UTC on
19 September 2026, exit code 0, one thread and a 4096 MiB limit. The exact
source hash is
`e5c888faffd3a0936d55c7cb9ec59d24ea54a60b204f921d5ee68734f5124d44`,
equal to frozen `Solution.lean`. The aggregate log hash is
`4332f3f7259395d8785cf3877b763a6bb831f30ecd8a857ff131e6598b8a7336`;
its output hash is
`949d0f37c03007a62655cf56c99208c73cc74d82d6697eaf0b9163723e104ac2`.
I checked the receipt source hashes and all declared transitive source hashes
against this packet, and checked current output hashes for its 86 proof
modules, including the aggregate. Most modules are explicitly reused
source-matched successful outputs, not freshly compiled in run 087.

Root then supplied the separate actual publication-name run 088. I inspected
its receipt (SHA-256
`72478dd92a3bce17b57c7bda2834aaf57052ff35745826e86248e2610448015e`),
the Solution log, and the Challenge log. The exact command is:

```text
/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean --threads=1 --memory=4096 -o /Users/georgestepaniants/Research/OpenProblemsInNLA/.local-recovery-20260918/local-lean/.lake/build/lib/lean/Solution.olean Solution.lean
```

The working directory was the recovery `local-lean` directory. Solution ran
from 07:51:35.271490 to 07:51:43.250652 UTC, exit 0, with the identical reviewed
source hash and byte-identical aggregate log. Its output hash is
`444ad1fadb76f93c7bbca6720f1867beb8075fd5d770be56a0c6ecb94cba658a`;
I checked that output hash. Challenge also elaborated with exit 0 and exactly
the expected 25 placeholder warnings; that is reference-header evidence only,
not proof evidence. The shared live Challenge source/output later differed
from this run, so I bind the Challenge claim to the frozen input hash and
the retained run receipt/log, not to the later mutable development files.

I inspected the hash and top-level metadata of root's recursive local replay
audit `LOCAL-REPLAY-AUDIT.json`
(`94021fa538957ad35044b9a6540fecf8a3ca99bcacd6546881cd3ac1b37e2cfa`).
I did not independently replay all historical compilation origins or rerun
the compiler. My independent source review and arithmetic checks stand apart
from that author's audit. The supplemental evidence JSON records these
precise scopes and hashes.

No GitHub run ID or Linux Comparator result for this frozen formalization
was inspected or claimed. Final Comparator/kernel/sandbox checks, the other
independent final referee, and truthful publication metadata remain separate
gates. This review changes neither the completed-verification count nor the
new-mathematical-resolution count.
