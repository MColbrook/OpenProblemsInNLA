# Stable quadratic branch: statement first

Manuscript Lemma 2 chooses a branch of a reciprocal quadratic. In its
notation set `a = kappa_l * sin(theta/2)` and use the explicit expression

`r(a) = (Complex.sqrt (1+a^2) - a)^2`.

For every complex `a` with positive real part, prove directly that this
expression is nonzero, has norm strictly less than one, and satisfies
`2-r(a)-r(a)⁻¹ = -4*a^2`. Also prove `r(0)=1`. The principal square root
must be the actual Mathlib function, with its square identity and positive
real part derived, not assumed as a branch certificate.

This is the manuscript's quadratic-formula choice since
`kappa_l^2 = -omega_l` and `4*sin(theta/2)^2 = 2-2*cos(theta)`.
The root-of-unity identity, actual parameter substitution, smoothness,
distinctness, conjugation and uniform exponential estimates are separate
remaining steps. This file is not yet the full statement of Lemma 2.
