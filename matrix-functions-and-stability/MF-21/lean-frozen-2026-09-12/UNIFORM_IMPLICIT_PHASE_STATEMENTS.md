# Statement lock: one uniform implicit phase

Locked before proof source on 20 September 2026. The coordinator approved
this interface. The source manuscript is unchanged. This is the actual
implicit equation in (4), used in Section 4, rather than a hypothesis that
an implicit phase already exists.

For every natural `m` with `1 <= m`, construct positive real numbers
`r`, `epsilon`, `C` and one total function `Y : (Real × Real) -> Real`.
Put

```
D = Ioo (-r/2) (pi+r/2) ×ˢ Ioo (-epsilon) epsilon.
```

Prove all of the following for this same function and these same constants:

1. `ContDiffAt Real ⊤ Y p` for every `p in D`.
2. For `p=(x,h) in D`, `Y p in Ioo (-r) (pi+r)` and
   `Y p = x + h * manuscriptEta m (Y p)`.
3. On `D`, `|Y p-x| <= C*|h|`.
4. For every `x in Ioo (-r/2) (pi+r/2)`, `Y (x,0)=x`.
5. For `p=(x,h) in D` and every `y in Icc (-r) (pi+r)`,
   `y=x+h*manuscriptEta m y` implies `y=Y p`.

The order `⊤ : ℕ∞ω` in this pinned Mathlib is the analytic order `ω`,
not the smooth order `∞`. The intended formal conclusion is literally
`ContDiffAt Real ⊤`, hence it implies the manuscript's required joint
C-infinity regularity. The actual existing `manuscriptEta_contDiffAt`
already has this analytic-order statement. No analyticity assumption
about a new or unspecified extension is added.

The uniform rectangle contains `[0,pi] × {0}` in its interior. In
particular the implicit phase works simultaneously for all real x in
the original closed interval and for h of either sign. A value outside
the rectangle is merely a totalization and carries no claim.

The first bounded component, `EtaNeighborhood.lean`, proves

```lean
theorem manuscriptEta_enlarged_interval_bounds (m : ℕ) (hm : 1 ≤ m) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ y ∈ Set.Icc (-r) (Real.pi + r),
        ContDiffAt ℝ ⊤ (manuscriptEta m) y ∧
        |manuscriptEta m y| ≤ C ∧
        |deriv (manuscriptEta m) y| ≤ C
```

The analytic locus is open by Mathlib's
`ContDiffAt.eventually` at order omega. Alternatively the concrete
finite intersection where the normalized phase factors have positive
real part gives an open analytic neighborhood. No inference that an
arbitrary C-infinity-at-a-point locus is open is permitted. The closed
interval can be enlarged slightly inside this neighborhood; compactness
then bounds the actual eta and its derivative on the enlargement.

The next generic scalar component uses only these proved regularity
and bound hypotheses. Choose epsilon so that
`epsilon*C <= r/4` and `epsilon*C <= 1/2`. For a point `(x,h)` of D,
`y -> y-h*eta(y)` has positive derivative on the enlarged interval,
and its values at the two endpoints strictly bracket x. The ordinary
intermediate value theorem and strict monotonicity give one unique
interior root. Choose that root pointwise and totalize outside D.

At any point of D, apply the pinned
`ContDiffAt.implicitFunction` to
`F ((x,h),y) = y-x-h*eta(y)`. Its partial derivative in y is
`1-h*deriv eta y`, strictly positive from the proved uniform bound.
The library's eventual equation and continuous local implicit solution,
together with the global interval uniqueness just proved, identify the
chosen root with the local implicit function on a neighborhood. The
library `contDiffAt_implicitFunction` then proves joint regularity of
the same Y everywhere in D. This is a genuine construction/gluing
argument, not a conclusion included among its hypotheses.

Before writing the generic source, its precise scope is fixed as
`uniform_implicit_scalar`: replace pi by a real `L>=0`, supply `r>0`,
`C>0`, and the three enlarged-interval regularity/value/derivative
properties displayed above for a scalar function `eta`. Its conclusion
supplies epsilon and Y with properties 1--5, with the same r and C and
with L in place of pi. This scalar helper assumes no solution function,
no implicit equation conclusion, and no derivative invertibility
conclusion. `ImplicitPhase.lean` will discharge every helper hypothesis
using `manuscriptEta_enlarged_interval_bounds` and `pi>=0`.

Finally the equation and eta bound give `|Y-x| <= C*|h|`; h=0 gives
the exact initial value. No expansion coefficients, uniform Taylor
remainder, eigenvalue approximation, or completed MF-21 target is
claimed here. Those remain separate obligations.

Source authors run no Lean compiler. The coordinator owns serialized
local tests; actual results and source hashes are recorded separately.
GitHub Comparator remains a separate unrun final check.

Prose erratum recorded after the successful local test: the frozen
`ImplicitPhase.lean` module comment calls the implicit equation (5).
Its correct manuscript number is (4); (5) defines the coefficients.
This comment-only discrepancy changes no definition or theorem. The
passed source is left byte-for-byte unchanged pending a later recorded
source-matched rerun.
