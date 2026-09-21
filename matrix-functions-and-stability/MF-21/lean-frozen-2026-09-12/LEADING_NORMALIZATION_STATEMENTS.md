# Leading normalization: statements fixed before proof

20 September 2026. This file locks the next algebraic bridge from manuscript
(15) to (16) and (18), without changing the frozen mathematical document.
The hypotheses are `m >= 2` and `0 < theta <= pi`, including the upper endpoint.
All roots, subsets, coefficients, products, and phases are the existing literal
definitions; no free coefficient, phase, or spectral assumption is introduced.

Write `Aplus` for `boundaryCoefficient` on `boundaryLeadingZIndices`, `Aminus`
for its inverse-unit counterpart, `Q = boundaryExteriorProduct`,
`U = boundaryPhaseMultiplier`, and `N = manuscriptNormalizer`.
The actual ordered-list signs are minus for Aplus and plus for Aminus.

The first statement is the exact normalization identity

```
N(m,n,theta) = Aplus(theta) * (2 * I * U(theta)) * Q(theta)^(n+m).
```

Indeed Aplus contains `-V(R)*V(O)*Q*z^(-(m-1))*conj(f)^2`, while
`U = exp(i*((m-1)*theta+2*psi))`. Their phases cancel, leaving the
manuscript's `(-2*I)*V(R)*V(O)*Q^(n+m+1)*normSq(f)`.
The polar identity uses the sum of the individual arguments, never the
principal argument of the product. Nonvanishing of N already has a proof.

The second statement is the exact sum of the two leading terms:

```
Aplus * (prod_{i in Splus} roots_i)^(n+m)
  + Aminus * (prod_{i in Sminus} roots_i)^(n+m)
  = N * (Real.sin (manuscriptPhaseFn m n theta) : Complex).
```

The phase is `(n+1)*theta-2*psi = (n+2)*theta-eta`. In particular the
normalization sign and the sine sign are fixed, not chosen after compilation.

Finally, for every cardinality-m subset S, prove

```
normalizedErrorCoefficient(S,theta) * boundaryProductRatio(S,theta)^(n+m)
  = boundaryCoefficient(S,theta) * (prod_{i in S} roots_i)^(n+m) / N.
```

This uses the previously proved equality of raw and normalized coefficient
ratios for theta nonzero, and actual N nonvanishing. It identifies the chosen
smooth weights with the literal quotient in (18). It does not by itself sum
the determinant expansion, assert reality of the finite error expression,
or prove the endpoint-zero condition, indexing, Taylor expansion, or MF-21.

All computations are symbolic ring/field/exponential identities. No numerical
interval computation or new trusted axiom is needed for this bridge.
