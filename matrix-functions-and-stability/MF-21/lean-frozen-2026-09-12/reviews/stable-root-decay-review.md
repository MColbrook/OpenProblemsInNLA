# Independent stable-root decay review

Verdict: **APPROVE**, for the scalar compactness lemmas, norm derivative,
and per-parameter exponential bound in `StableRootDecay.lean`.

Reviewer: `/root/mf21_restart_lean_audit`, 20 September 2026. I did not
author or edit this module and launched no compiler. I inspected its
entire final source, locked statements, the relevant pinned Mathlib
`dslope`, squared-norm derivative, and extreme-value APIs, and the actual
successful local log. The review follows the pinned referee standard,
SHA-256 `e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Exact source scope

Paths are relative to `MF21-restart`.

| Path | SHA-256 |
| --- | --- |
| `MF21Restart/StableRootDecay.lean` | `edb5b83593d2d7a8dc43e20ec4c77909a8c49662218342683d5e2f1d89911bb2` |
| `STABLE_ROOT_DECAY_STATEMENTS.md` | `7b437edbcf879ea7eb3b66254d83d663b938a62ce0e8d8ccab5487ab49c37304` |
| `MF21Restart/StableRootSmooth.lean` | `241296dc3b8ac1ca554a1685162f9952d7e4825d170abf56cba8d54f233f4011` |
| `original-proof/solution.md` | `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa` |
| `evidence/logs/stable-root-decay-02.log` | `b586bbfa14200820c9510ba05f3b5163ad461b56a0c19e59dd04d6e170095db0` |

## Compactness really supplies a uniform positive constant

`StableRootDecay.lean:21–27` assumes continuity of f on `[0,L]`,
`f(0)=1`, an actual derivative `d<0` at zero, and `f(x)<1` at each
`0<x<=L`. It assumes neither a uniform gap nor the desired decay.
Full monotonicity is not assumed or needed. These are satisfiable
hypotheses, for example for `f(x)=exp(-x)` and positive L.

At lines 28–33, `dslope f 0` is continuous on the interval. Mathlib's
definition is the difference quotient away from zero, extended by the
actual derivative at zero (`Analysis/Calculus/DSlope.lean:32–47`).
Continuity at zero follows from the proved differentiability there;
continuity elsewhere follows from f's within-interval continuity and
the nonzero denominator. There is no division by zero at the endpoint
and no assumption that a discontinuous quotient has a continuous extension.

Lines 34–46 prove strict negativity at **every** point, using `d<0`
at zero and `x*dslope f 0 x = f(x)-1<0` for positive x. Lines 47–50
take an attained maximum on the nonempty compact interval and define
`c` as its negative. Since the attained value is strictly negative,
this proves `c>0`; merely having a nonpositive supremum would not have
been sufficient. The maximum argument therefore supplies a single c
independent of x.

Lines 51–59 multiply the maximum inequality by `x>=0`, obtaining the
claimed `f(x)<=1-c*x`. This includes x=0, where both sides equal 1.
The identity used at that endpoint is Mathlib's unconditional
`sub_smul_dslope`, not a cancellation requiring x to be positive.

Lines 62–76 derive the exponential inequality with the **same** positive
c from `1-c*x<=exp(-c*x)`. The signs and inequality direction are
correct. The scalar lemma need not assume f is nonnegative: the
transitive upper-bound argument is valid for any real-valued f meeting
its hypotheses. The subsequent root-norm specialization is nonnegative
automatically.

## Actual root curve and zero-endpoint derivative

Lines 79–90 derive
`d/dθ |stableRootCurve κ θ| at 0 = -Re κ`
from the previously proved complex-valued derivative `-κ` and value 1.
The real squared-norm derivative is `2*Re(conj(1)*(-κ))=-2*Re κ`.
Taking its real square root is legitimate at the nonzero squared norm
1, and `sqrt(norm²)=norm` identifies the differentiated function on
its domain. No differentiability of the norm at a zero vector is used.
This derivative statement is valid for every κ; its sign only becomes
negative when `Re κ>0` in the decay theorem.

Lines 94–103 instantiate all scalar hypotheses for the **actual**
principal-branch root curve, using its proved smoothness, endpoint value,
norm derivative, and strict unit-disk inclusion. The resulting statement
has quantifier order

`for each κ with Re κ>0, there exists c>0, for all 0<=θ<=π, |rκ(θ)|<=exp(-c*θ)`.

Thus c is uniform over the entire closed θ interval, including zero
and π, but may depend on κ. No exponential root estimate was supplied
as an input. This implements the compactness step explained immediately
after manuscript (8), `solution.md:93–101`.

The locked statements match these four declarations exactly. A common
constant for **all** published indices `1<=ell<m` still requires taking
a positive minimum over that finite collection of κ values. Root powers,
logarithmic-derivative bounds, determinant prefactors and derivative
estimates are also separate obligations. Accordingly this module does
not yet prove the entire quantified manuscript Lemma 2 or the boundary
remainder estimate.

## Trust and verification status

The coordinator reports that the actual serial `stable-root-decay-02`
process exited 0. I independently inspected its hashed log: all four
public axiom reports contain exactly `propext`, `Classical.choice`, and
`Quot.sound`, with no errors or `sorryAx`. The exact current source was
rehash-checked after review. Static inspection found no `sorry`, `admit`,
custom axiom, unsafe shortcut, `native_decide`, or legacy/Challenge import.

This independent approval is limited to the specified source bytes and
partial analytic statements. It does not claim a GitHub Comparator run,
a completed MF-21 Target, or an additional completed original problem.
