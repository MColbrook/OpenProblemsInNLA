# Exact finite eigenvector criterion: statement first

Frozen manuscript Section 2, the assertion following equation (13).

For `m≥1`, `n≥0` and a complex spectral parameter `lam`, let
`w : Fin (2*m) → ℂ` be injective, nonzero, and satisfy
`(2-w i-(w i)⁻¹)^m = lam` for every `i`. Prove the equivalence:

* `det (boundaryMatrix m n w) = 0`;
* there is a nonzero vector `v : Fin n → ℂ` such that the complexification
  of the original integral-defined `toeplitz m n` maps `v` to `lam • v`.

All bridges are required: actual characteristic-root identity, recurrence
basis, extension/restriction with the precise ghost conditions, pointwise
normalization of the Fourier recurrence, and exact finite convolution
identity. No eigenvalue criterion may be introduced as an extra hypothesis.

Construction and smoothness of the manuscript's particular root list,
and its distinctness for `0<theta<pi`, remain later obligations. Repeated
roots at either endpoint are outside this distinct-root equivalence.
