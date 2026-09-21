# Canonical eigenvalue accessor: statement first

For every natural `m,n` and real `lam`, prove that

`∃ j, 1≤j ∧ j≤n ∧ eigenvalue m n j = lam`

is equivalent both to membership in `orderedEigenvalueList m n` and to
being a root of the characteristic polynomial of the actual real
`toeplitz m n`. Use the existing Hermitian spectral theorem and the exact
sort/list definitions. Neither an omitted smallest eigenvalue nor the
totalized value outside `1≤j≤n` may witness these statements. The `n=0`
case must remain empty on both sides.

This checks the connection to actual finite-matrix eigenvalues. It does
not prove eigenvalue positivity, asymptotics, simplicity, or phase indexing.
