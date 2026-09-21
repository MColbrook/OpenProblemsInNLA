# Exact leading coefficient factorization (15)

Statement lock before `MF21Restart/LeadingBoundaryCoefficients.lean`.
Use the frozen actual `boundaryCoefficient`, leading index sets and their
proved inherited orders/signs, `stableRootList`, `exteriorRootList`,
`boundaryExteriorProduct`, and `manuscriptPhaseProduct`.

For fixed m≥2 and any real theta, write only as explanatory abbreviations:

- z = `oscillatoryRoot theta`;
- R = `stableRootList m theta`, O = `exteriorRootList m theta`;
- VR = `(Matrix.vandermonde R).det`, VO = `(Matrix.vandermonde O).det`;
- Q = `boundaryExteriorProduct m theta`;
- f = `manuscriptPhaseProduct m theta`.

Prove the conjugation identity

```text
∏ ell : Fin(m-1), (1 - R ell * z) = (starRingEnd ℂ) f.
```

It must follow by reversing the actual stable-root indices under complex
conjugation and using conjugation of the actual unit exponential. Do not
replace a sum of arguments by the principal argument of a product.

Prove the two exact coefficient identities, with no root-value or phase
assumptions:

```text
boundaryCoefficient m (characteristicRoots m theta)
  (boundaryLeadingZIndices m ...) =
  -(VR * VO * Q * (z⁻¹)^(m-1) * ((starRingEnd ℂ) f)^2)

boundaryCoefficient m (characteristicRoots m theta)
  (boundaryLeadingZInvIndices m ...) =
  VR * VO * Q * z^(m-1) * f^2.
```

These are manuscript (15) with its unspecified sigma fixed to -1 by the
actual inherited ordering. Derive the exact root tuples from
`LeadingBoundaryIndices`: complement Splus=(R,z⁻¹), Splus=(z,O),
complement Sminus=(R,z), Sminus=(z⁻¹,O). Use proved Vandermonde
prepend/append identities and exact finite-product algebra. The values
of R are genuinely nonzero, and Q must be identified with the actual
product over O, rather than postulated to equal it.

Optional direct product helpers may prove that the selected root products
for Splus and Sminus are respectively z*Q and z⁻¹*Q; these follow from
the actual insert definitions and prepare (16). No determinant normalizer,
coefficient ratio, or desired leading factorization may be assumed.

The identities are algebraic and valid for all real theta, including zero
and pi; they do not require the full root list to be distinct there. This
module does not claim nonvanishing of the leading coefficients at zero,
the real normalized determinant identity, bounds for coefficients, or the
full MF-21 target. No compiler process or edits to another module are
authorized for this source task.
