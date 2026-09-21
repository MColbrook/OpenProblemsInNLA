# Proposed statement-first decomposition of manuscript Lemma 4

This is a proof-development proposal, not a claimed theorem or a replacement
of the original proof. The manuscript is unchanged. No source below is
assumed to exist merely because a proposed name is given. The coordinator
owns the leading-term, normalizer, and determinant decomposition.

## Existing inputs and necessary missing input

The actual root list, boundary criterion, kernel/eigenspace dimension
equality, determinant multiplicity implication, and equality between
eigenspace dimension and multiplicity in the sorted eigenvalue list are
already available in `ConcreteBoundary`, `SimpleDeterminant`, and
`EigenvalueMultiplicity`. `PhaseMonotonicity` supplies (20) and a uniform
bound on eta. `BoundaryErrorBounds` supplies (11) for the actual finite
complex expression.

The current tree does not yet prove that every actual eigenvalue belongs
to `(0,4^m)`. The boundary criterion for angles in `(0,pi)` alone cannot
replace that assertion. `SpectralEnclosure` should first prove positive
definiteness of the actual Fourier Toeplitz matrix and its upper complement,
then the strict enclosure for each published index. This follows the
quadratic-form argument at manuscript line 219, not an assumption that
there are already n eigenangles.

Prove also that `symbol m` is continuous and strictly increasing on
`[0,pi]` for `m >= 1`, with endpoints zero and `4^m`. The elementary
ingredients are `Real.strictMonoOn_sin` on the half-angle interval,
strict monotonicity of a positive natural power on nonnegative reals,
and the intermediate value theorem. This gives exactly one angle in
`(0,pi)` for every in-range eigenvalue. An eigenangle accessor, if useful,
should be a new proof-side definition with proved specifications; do
not change `Definitions.lean` or the one-based eigenvalue convention.

## 1. Real residual and the endpoint improvement

Use the coordinator's determinant decomposition to identify

```text
H(m,n,theta) = sin(manuscriptPhaseFn m n theta)
                + (boundaryErrorExpression m n hm theta).re
D(m,n,theta) = manuscriptNormalizer m n theta * (H(m,n,theta) : Complex)
```

on `0 < theta <= pi`. The complex error's reality is a proved consequence
of conjugation; it must be supplied when passing from real residual zeros
to complex determinant zeros. Derive `E(pi)=0` from the actual artificial
determinant zero, the nonzero normalizer, and `F(pi)=(n+1)*pi`.

Lock a separate theorem giving exactly (12): there are positive c,C
depending only on m such that, for every n and `pi/2 <= theta <= pi`,

```text
norm(error theta) <= C*(n+1)*(pi-theta)*exp(-c*n*pi/2).
```

Use the genuine derivative bound from `BoundaryErrorBounds` on
`[theta,pi]`, endpoint zero, and the norm mean-value bound (or the
fundamental theorem of calculus). This sharp endpoint factor is necessary:
the value bound from (11) alone cannot exclude roots arbitrarily close
to the artificial root pi.

## 2. Uniform small error in the upper phase range

Lock the following actual statement, with no assumed error bound:

```text
exists J N : Nat, 1 <= J and J <= N and
  forall n >= N, forall theta in [0,pi],
    J*pi-pi/4 <= F(n,theta) ->
      abs(E(n,theta)) < 1/4 and
      abs(deriv(E n) theta) < (n+2)/8.
```

Choose N to include the existing derivative-bound threshold and `N >= 2`.
If `abs(eta theta) <= B`, then for these n,
`n*theta >= (J*pi-pi/4-B)/2`. Pick J using exponential decay as J tends
to infinity; c and C remain independent of n and theta. The library has
`Real.tendsto_exp_neg_atTop_nhds_zero` and `Real.tendsto_exp_atBot`.
An explicit logarithmic cutoff is unnecessary.

## 3. One simple residual zero in each phase window

For n beyond that threshold and `J <= k <= n`, define the window by

```text
theta in [0,pi] and abs(F(n,theta)-k*pi) <= pi/4.
```

First prove that its two boundary phase values `k*pi +/- pi/4` have
unique preimages `a_k,b_k` in `(0,pi)`, using the actual endpoint values
and strict monotonicity of F. The window equals `[a_k,b_k]` and is
nondegenerate. This avoids treating an arbitrary preimage set as an
interval without proof.

Lock the conclusion that there is exactly one theta in this window with
`H(n,theta)=0`, that it lies in `(a_k,b_k)`, and that
`deriv (H n) theta != 0`. The signed derivative
`(-1)^k * deriv(H n)` is positive on the entire window. Use the sine
addition formulas at `k*pi`, the cosine lower bound on `[-pi/4,pi/4]`,
the actual lower derivative bound for F, and the small derivative error.
Exact `sqrt(2)/2` is available from `Real.sin_pi_div_four` and
`Real.cos_pi_div_four`; a proved weaker bound `1/2` also leaves enough
margin and requires no numerical certificate. Endpoint signs give
existence by `intermediate_value_Icc`; positive signed derivative gives
uniqueness by `strictMonoOn_of_deriv_pos`.

Obtain a nonzero determinant derivative from `D=N*H`, `H(theta)=0`,
the ordinary differentiability of both factors in the interior, and
`N(theta)!=0`. Instantiate the actual matrix-curve derivative and
`SimpleDeterminant`, then `EigenvalueMultiplicity`, to prove that this
root corresponds to exactly one position in the actual sorted list.
Do not infer algebraic multiplicity one from existence/uniqueness of a
real zero alone.

## 4. Exclude all remaining roots in the upper range

Separate the elementary real phase partition from spectral arguments.
On each gap between the windows, through phase
`(n+1)*pi-pi/4`, prove `abs(sin F) >= 1/sqrt(2)` and use `abs(E)<1/4`.
A finite-interval partition or an explicitly bounded nearest-integer
construction may be used; do not omit uncovered boundary points.

For the final window centered at `(n+1)*pi`, with theta less than pi,
set `delta=(n+1)*pi-F(theta)`. Then `0 <= delta <= pi/4`. The lower
derivative bound gives

```text
delta >= (n+2)/2 * (pi-theta),
abs(sin F(theta)) = sin delta >= (n+2)/pi * (pi-theta).
```

The sine inequality follows from `Real.mul_le_sin`. The same phase-width
and derivative estimate place this window above pi/2. The endpoint error
bound from step 1 is strictly smaller for all theta below pi once n is
large. Cancel the positive factor `pi-theta` only for theta < pi. The
endpoint pi itself is an artificial determinant root and is excluded
from the spectral claim.

Combine these facts into an exact classification: every interior zero
whose phase is at least `J*pi-pi/4` is the unique zero of one window
with index k in `[J,n]`. This should be a separate public result before
attempting any identification with the k-th eigenvalue.

## 5. A bounded finite-order counting lemma

Prove the following generic finite-order lemma separately. Let
`lambda : Fin n -> Real` be monotone, let `1 <= J <= n`, and let
`mu : Nat -> Real` be strictly increasing on `[J,n]`. Suppose each
`mu k` occurs at exactly one index of lambda, and every lambda value at
least `mu J` equals some `mu k` with `J <= k <= n`. Then

```text
forall k, J <= k -> k <= n -> lambda (k-1) = mu k.
```

All accesses must use a bounded `Fin n` proof, not an out-of-range
default value. A bijection between the k-tail and the corresponding
upper-level index set, or downward induction from the maximum, proves
the statement without restrictions on smaller entries or repetitions
below `mu J`. Library ingredients include `List.SortedLE.monotone_get`,
finite cardinality and the existing count/unique-index theorem.

Instantiate lambda with `orderedEigenvalue m n` and
`mu k = symbol m (the unique root in window k)`. Root order follows
from strict phase monotonicity and disjoint ordered windows; symbol
strict monotonicity transfers it to eigenvalues. Spectral enclosure
supplies an interior eigenangle for every remaining list entry.
The determinant criterion and step 4 discharge the upper-tail coverage.
This is exactly the manuscript's downward counting argument at line 249;
no claim about where the first `J-1` roots lie is needed.

## 6. Quantitative phase and angle errors

At the root with its now-proved published index j, let
`delta=F(theta)-j*pi`. The window gives `abs(delta)<=pi/4`, and the
actual residual equation plus `Real.mul_le_sin` gives
`abs(delta) <= (pi/2)*C*exp(-c*n*theta)`. Bounded eta gives
`n*theta >= (j*pi-pi/4-B)/2`, hence a bound `C'*exp(-c'*j)` with
`c'=c*pi/2 > 0` and an adjusted positive C'.

Define the exact phase center y by its unique preimage equation
`F(n,y)=j*pi`. The lower derivative bound and
`Convex.mul_sub_le_image_sub_of_le_deriv` imply

```text
abs(theta-y) <= C''*exp(-c'*j)/(n+2).
```

From `F=(n+2)*theta-eta` and the window bounds, both theta and y are
positive and at most `C'''*j/(n+2)` because `j>=J>=1`. Lock this first
for the exact phase center, so its inverse equation is fully proved.

The smooth implicit function Y from the manuscript has not yet been
constructed in the current tree. Its later construction must establish
that `Y(mesh n j, 1/(n+2))` lies in `[0,pi]` and solves the same phase
equation. Uniqueness then identifies it with y. That bridge, rather than
a new assumption that y already equals Y, completes the literal (19).

## Suggested bounded implementation order

1. `SpectralEnclosure` and symbol monotonicity / exact inverse specification.
2. Endpoint error vanishing and estimate (12), after coordinator decomposition.
3. A scalar phase-window lemma and actual uniform-smallness instantiation.
4. Final-window exclusion and exact upper-root coverage.
5. Generic finite monotone-tail counting, then actual index identification.
6. Phase-center error bound, followed later by the constructed Y bridge.

The generic scalar and finite-order helpers may have explicit hypotheses;
the concrete final theorems must discharge them from the actual manuscript
functions. No helper or partial ingredient increases the count of verified
original targets. This proposal contains no Lean compilation or Comparator
claim.
