# Fresh mathematical audit of the September 12 MF-21 manuscript

Review completed: 2026-09-21 UTC.

Reviewed file: `/private/tmp/mf21-september12-solution.md` (398 lines).

SHA256: `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`.

Source commit supplied for this audit: `eb37bc17a462177f57efa270e9a9f9b17e9d88e2`. The file hash was independently checked with `shasum -a 256`; source-commit identity comparison belongs to the separate parent audit.

## Verdict and scope

**No mathematical error found in the stated Theorem 1.** I read the exact frozen manuscript, independently reconstructed its main derivations, and specifically challenged normalization, zero counting, endpoint control, uniform constants, and the trace obstruction. I found no false equation, invalid inference, missing essential premise beyond the explicitly cited external theorem, or quantifier error in the stated same-coefficient-family conclusion.

This is an informal mathematical audit. It is not Lean verification, an audit of a Lean translation, external human peer review, or a novelty search. I did not read previous reviews or later manuscript versions, inspect verification/status claims as evidence, edit the manuscript or Lean sources, or run a compiler. No numerical calculation was used as evidence.

## Checks of the vulnerable steps

1. **Stable roots and phase, lines 85–110, (6)–(8).** The nontrivial roots of unity cannot produce a unit-circle root or a repeated quadratic root for positive theta. The chosen square root has positive real part. The identity for `kappa_l + i` is correct, and its arguments sum to `(m-1)pi/4`. Conjugate pairing gives the phase value zero at pi. The compactness argument for an exponential modulus bound is valid with constants depending on fixed m. Smoothness of the argument at zero follows after dividing its factor by theta; no singular logarithmic derivative survives in the phase.

2. **Boundary determinant and normalization, lines 149–215, (13)–(18).** Shifting the ghost indices really gives bottom exponents `n+m,...,n+2m-1`. For the first dominant subset, the coefficient is `sigma V(R)V(O) Q z^{-(m-1)} conjugate(f)^2`. Multiplication by `(Qz)^{n+m}` therefore gives phase `(n+1)theta-2psi`, exactly as stated. The other term has the opposite Laplace sign and conjugate phase, so their sum is precisely the normalizer times `sin F_n`. There is no missing power of Q, factor of z, or index shift.

   At zero, the denominator's vanishing order is `(m-1)(m-2)+2(m-1)=m(m-1)`, matching each numerator. The listed first root derivatives are pairwise distinct, so the leading factors are nonzero and the normalized coefficients and their first derivatives extend smoothly. At pi the normalizer stays nonzero despite the two oscillatory columns coinciding. Non-dominant product moduli obey (17); their bounded logarithmic derivatives give both estimates in (11). The conjugation signs make the quotient real. The exact endpoint cancellation gives (12), rather than only a nonvanishing exponential bound.

3. **Multiplicity and indexing, lines 219–257, (19)–(20).** The recurrence/ghost restriction is injective and surjective onto the finite eigenvector kernel. A simple determinant zero forces boundary nullity one, and symmetry then supplies algebraic simplicity. A fixed sufficiently large J controls both the error and its derivative on the whole stated range. The phase intervals have one root each; the intervening gaps have none. In the final interval, both the sine lower bound and the error have a factor `pi-theta`, so the artificial root at pi does not hide an eigenvalue arbitrarily close to it. Counting downward from the n eigenvalues identifies interval k with eigenvalue k without an assumption about the unresolved lower intervals.

4. **Circulant comparison and uniform expansions, lines 259–308, (21)–(25).** The chosen circulant has no wrapped Fourier coefficient in the principal block. Its ordered eigenvalue formula handles both parities of its size, and `floor(j/2) >= j/3` holds for j at least two. The implicit-function construction has a common neighborhood on the compact x interval. At the sampled indices, its solution equals the unique interior phase root. The coefficient vanishing estimates follow from the chain rule; the finitely many small j are covered by interlacing. The factor `j^(2m-1) exp(-cj)` is uniformly bounded, and on the logarithm-squared range it is `O(h)`. Constants need not be uniform in m, and the theorem does not claim that they are.

5. **External inverse-kernel input, lines 312–333, (26)–(28).** I checked the primary [Böttcher–Widom preprint](https://arxiv.org/pdf/math/0412269), formula (5) and the paragraph on printed page 4 immediately preceding (13). It expressly states the required `L-infinity([0,1]^2)` convergence for the pure symbol, not merely convergence of operator norms. Its kernel and endpoint-index convention match the manuscript. The diagonal substitution in (28) is correct.

6. **Diagonal trace and critical contradiction, lines 335–380, (29)–(33).** The diagonal inference does not improperly restrict an arbitrary almost-everywhere bound to a null set: each approximating kernel is constant on a grid square, and continuity of the limiting kernel transfers the essential bound to its diagonal points. The diagonal integral equals `n^(-2m) trace(A_n^(-1))`; replacing n by n+2 has limiting factor one. The beta integral in (29) has the correct factorials.

   Under the assumed critical estimate for the same coefficients, (23) implies (30) for every fixed j. Interlacing supplies an n-independent summable majorant for all j at least two, while (30) supplies the first term. Thus the counting-measure dominated-convergence step is legitimate. Both parity decompositions of the shifted series are correct. Their removed finite sums are nonzero positive rational numbers for the stated m. Euler's formula and transcendence of pi therefore make (31) irrational, contradicting the rational value (29).

## Quantifiers and compressed justifications

Section 5 contradicts a full-range critical estimate for the coefficient family constructed in (5). This is exactly the conclusion stated in Theorem 1, which uses the same family throughout. It is not a quantifier error to refrain from separately claiming impossibility for every alternative continuous family. If that stronger statement were wanted, the bulk expansion supplies it through the usual coefficient-uniqueness induction along grids tending to an arbitrary interior x; continuity then includes the endpoints. That additional claim is unnecessary for the explicitly stated theorem. I also inspected [BBGM, Conjecture 8.4 and the surrounding discussion](https://arxiv.org/pdf/1710.05243) for this distinction.

The positivity of Q, the matching of the implicit solution to the interior phase root, and the harmless n-to-n+2 change in the trace scaling are concise rather than fully expanded in the manuscript. Each follows from information already present: conjugate root pairs (and a positive real root when present), uniqueness of the monotone phase equation, and a scalar ratio tending to one. I found no essential gap in these compressed steps.
