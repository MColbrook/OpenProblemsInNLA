# Finite inverse proved locally; uniform kernel limit still unproved

This is research toward proving the cited kernel-limit input of the frozen
manuscript. It is not a change to that manuscript or a completed MF-21
verification. The finite identity is now proved in Lean; the limit is not.

Primary-source check (20 September 2026): Böttcher--Widom, Section 2,
[paragraph before (13)](https://arxiv.org/html/math/0412269), explicitly
attributes the direct b=1 uniform-kernel proof to A. Böttcher, *The constants
in the asymptotic formulas by Rambour and Seghier for inverses of Toeplitz
matrices*, IEOT 50 (2004), 43--55, using a Duduchava--Roch inverse formula.
The original 2004 derivation has not been formalized here. The comparison
to a later primary statement of the inverse formula is recorded below.
The uniform-convergence input itself is stated in the cited source;
it is not presently formalized in this project.

Subsequent source comparison: formula (22), p. 181, of Böttcher, Fukshansky,
Garcia and Maharaj, [*Toeplitz determinants with perturbations in the corners*](https://www1.cmc.edu/pages/faculty/lenny/papers/toeplitz.pdf),
JFA 268 (2015), specializes at delta=gamma=m to the candidate below.
This identification follows by cancelling the displayed Gamma prefactor
against the two diagonal factors and converting positive-integer Gamma
values to rising factorials. Thus the formula is a known Duduchava--Roch
identity, not a new claimed discovery. Its local Lean proof is recorded below.

Write `(a)_r = a(a+1)...(a+r-1)` and use one-based indices. The exact
inverse for `A_ij=(-1)^(i-j) choose(2m,m+i-j)` is

```
G_ij = (i)_m (j)_m / ((m-1)!)^2
       * sum_{k=max(i,j)}^n (k-i+1)_(m-1) (k-j+1)_(m-1) / (k)_(2m).
```

Exact rational matrix multiplication checked `A*G=I` for all 60 pairs
`1<=m<=6`, `1<=n<=10`. The finite check is recorded in
`evidence/inverse-formula-finite-check.json`; it does not establish the formula
for arbitrary dimensions. No Lean theorem uses these tests as a premise.

A possible analytic proof reduces to one finite binomial identity. Let
`B_ik=choose(k-i+m-1,m-1)` for k>=i and zero otherwise, and
`U=diag((i)_m) B`, `D_kk=1/(k)_(2m)`. The candidate is `U D U^T`.
The inverse of B is the finite difference matrix `(I-shift)^m`, whose entries
are `(-1)^(k-i) choose(m,k-i)`. Consequently the needed inverse identity is

```
sum_{k=1}^{min(i,j)} choose(m,i-k) choose(m,j-k) (k)_(2m)
  = (i)_m (j)_m choose(2m,m+i-j),
```

with zero binomial convention for out-of-range lower indices. The common
sign is `(-1)^(i+j)=(-1)^(i-j)`. Both the finite-matrix inverse algebra and
the weighted identity now have local Lean proofs.

For d=i-j>=0 the identity is equivalently the polynomial identity

```
sum_{r=0}^{m-d} choose(m,r) choose(m,d+r) (j-r)_(2m)
  = choose(2m,m+d) (j)_m (j+d)_m,
```

where rising factorials on integer arguments extend the finite sum across
terms that vanish. `WeightedBinomialInverse.lean` now proves this polynomial
identity and the one-based finite identity with i=j+d, m,j>=1 and every
natural d, including the zero case d>m. It uses an explicit telescoping
certificate, positive-integer induction, and polynomial equality, with no
hypergeometric or sampling assumption. The successful actual local run is
`evidence/logs/weighted-binomial-inverse-02.json`; independent source review
is `reviews/weighted-binomial-inverse-coordinator-review.md`. This module
does not by itself prove a matrix inverse or uniform limit.

The pinned Mathlib module `RingTheory/PowerSeries/WellKnown.lean` already
provides `PowerSeries.invOneSubPow` with coefficients
`choose(m-1+d,m-1)` and inverse `(1-X)^m`. This offers a reusable route to
the upper triangular factor B and its inverse, avoiding a new alternating
binomial-sum proof. `TriangularInverse.lean` proves both finite matrix
products equal one. `FourierBinomialStencil.lean` proves the binomial formula
for the actual integral Fourier coefficient. `ToeplitzWeightedFactorization.lean`
then proves T-transpose W T = P A P for the actual A. `MatrixInverseAlgebra.lean`
and `ToeplitzInverse.lean` discharge every inverse hypothesis and identify
the actual nonsingular inverse. `InverseKernelEntries.lean` gives the
rising-factorial entries above and exact simultaneous index reversal.
All have successful local component records and scoped independent reviews.
The 83-module integrated run including them passed locally; its record is
`evidence/runs/20260920T221851486781Z/record.json`.

Scaling the explicit positive sum should give the integral kernel in (27)
through a uniform Riemann-sum argument. Uniform control near t=0, boundary
cells, and the diagonal remain obligations. This route would prove
the external input actually used by the manuscript, rather than assume a
trace limit. Attribution and prior literature must be checked before any
novelty claim; none is made here.

## Remaining uniform-limit route (not a proof claim)

Let h=1/n and x_i=(i+1)/n for zero-based Fin n indices. Define
`R(r,h,x)=product_{a<r}(x+a*h)`. Exact scaling gives
`R(r,h,h*x)=h^r*(x)_r`, without division or an h!=0 premise.
The rescaled inverse is h times a finite sum of the rational polynomial
integrand recorded in SCALED_RISING_STATEMENTS.md. At h=0 this is exactly
the integrand in (27), including its factorial prefactor.

On x+y>=1 the integration variable is at least 1/2. Riemann cells need
a collar down to 1/4 once n>=4. On h,x,y in [0,1], t in [1/4,1], the
denominator is strictly positive. Compact uniform continuity can bound
all parameter errors and cell oscillations; no numerical subdivision or
explicit large derivative constant is required. ScaledRising.lean passed
local test02 with nine standard-axiom reports. RiemannCellBound.lean passed
test03 for the exact symbolic cell-error sum bound. ScaledInverseSum.lean
then passed test01 for the exact identity h^(2m-1) A-inverse = h times the
concrete integrand sum, including its two shifted differences. Applying
uniform continuity to the sum and the moving integration endpoint remains
unproved.

Define the candidate continuous kernel on x+y>=1 by the literal integral
and below that line by reflection. On the common boundary y=1-x,
reflection merely swaps x and y, so symmetry of the integral makes the
pieces agree. Prove continuity on both closed halves, then glue. The
exact finite inverse reversal reduces the other half to the first; its
one-based coordinate shift is h and must be controlled, not omitted.
The matrix step-kernel ceiling/clamping convention at boundary cells
also requires an explicit uniform distance estimate. These steps should
establish the manuscript's essential-uniform input, after which the
diagonal passage and trace integral remain to be assembled.
