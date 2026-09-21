# Statement lock: exact normalized boundary coefficients

Define `characteristicRootSlope m i = dslope (fun theta =>
characteristicRoots m theta i) 0`. This is an actual divided difference,
with its derivative value at zero. Prove real analyticity and smoothness
for m >= 2, its value at zero is `characteristicRootTangents m i`, and
`characteristicRoots m theta i = 1 + theta * characteristicRootSlope m i theta`.

For an arbitrary inherited root sublist `u : Fin k -> Fin (2*m)`, define
the normalized Vandermonde as the determinant of the slopes on that list.
Prove its smoothness and exact factorization of the original Vandermonde
by `theta ^ vandermondeDegree k`. For an injective sublist its zero value
is nonzero, using the proved injective tangent list. This includes empty
and singleton lists.

For every subset S of cardinality m, define the normalized boundary
coefficient as the actual Laplace sign times the normalized Vandermonde
of the inherited complement and of S. Prove that the actual
`boundaryCoefficient m (characteristicRoots m theta) S` equals
`theta ^ (m*(m-1))` times this normalized coefficient, for every real theta.
Prove smoothness and a nonzero value at zero. No determinant estimate,
quotient bound, or assumed leading-order expansion is a hypothesis.
