# Independent review: the actual uniform Taylor family

Verdict: **APPROVE** ParametricTaylor02 and ImplicitTaylor01 at the
exact hashes below. They prove the manuscript's derivative/factorial
coefficients and uniform Taylor remainder (23) for the constructed
actual implicit phase. One Y, one coefficient family, and one positive
h-neighborhood work for all orders. There is no exponential factor in
the Taylor remainder.

Reviewer: `/root/mf21_restart_lean_audit`, 20 September 2026. These
modules were authored by the other source agent, with coordinator
elaboration fixes. The reviewer edited no source and ran no compiler.
The pinned standards have SHA256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Exact sources and actual local evidence

| Artifact | SHA256 |
|---|---|
| `IMPLICIT_TAYLOR_STATEMENTS.md` | `df46a97a9b355c03d32f4c921c7734913c351cdac039dcfbe6de2d4b59c0be5b` |
| `MF21Restart/ParametricTaylor.lean` | `1725fa819dfa0acef69e7ff312d68021eee5a332ce9f66b0c501bd995a7ae5fc` |
| `evidence/logs/parametric-taylor-02.json` | `e67a55f9343e2bfe3b35d7fcf0d73f2853490249d2412bf7f33d86e3bf4a603c` |
| `evidence/logs/parametric-taylor-02.log` | `4ca933f6bbc3dae47d5d817f717069ad9d70d7c49aca4eb6f64a6bd544fa51db` |
| `.lake/build/lib/lean/MF21Restart/ParametricTaylor.olean` | `65aaae225a832cbb853fa34c3f6d66cc463ca9a1133a201812d20dfaf5dd3bd6` |
| `MF21Restart/ImplicitTaylor.lean` | `f91067cf235fc4afd4b869a8b605a15a46a9c0405484550ad10db351d0d2296d` |
| `evidence/logs/implicit-taylor-01.json` | `f06c6c7eae7744edf9cc53b6db79db3980d5bad5df0c054d01791400b14bde64` |
| `evidence/logs/implicit-taylor-01.log` | `21884389636e8f5d56e0c6c86fc06f25de912c66b735f474e885ea5ebd92a7c3` |
| `.lake/build/lib/lean/MF21Restart/ImplicitTaylor.olean` | `b292f28a1349293bf7a15ecd83ce92ef3e6903add269c5711463fcbd475c04ab` |

The reviewer recomputed every hash and matched current source, log and
compiled output to the successful local records. Both record exit 0,
unchanged source, `LEAN_NUM_THREADS=1`, and command
`lake env lean -j1 -M4096 -o
.lake/build/lib/lean/MF21Restart/<Module>.olean MF21Restart/<Module>.lean`.
The three ParametricTaylor reports and single ImplicitTaylor report
contain only `propext`, `Classical.choice`, and `Quot.sound`.
ParametricTaylor's unused hL warning is harmless: it records the natural
nonempty-interval convention, while the bound is also vacuous for
negative L. No derivative or Taylor premise is missing. Comparator
has not run.

The unchanged manuscript SHA256 is
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`.
The source matches its coefficient equation (5), lines 59–66, and
uniform Taylor equation (23), lines 280–286. Vanishing equation (24)
and spectral comparison (25) are explicitly separate.

## Statement and proof findings

1. `ParametricTaylor.lean:19–23` defines literal one-variable
   iterated derivatives in h and divides the k-th derivative at
   zero by k!. It does not use an arbitrary formal power-series
   coefficient or an order-dependent approximation family. The
   direction of differentiation is h, with x held fixed.

2. Lines 27–56 prove joint analytic regularity of those vertical
   derivatives by induction. At the successor step, the map
   `((x,h),t) -> verticalIteratedDeriv F k (x,t)` uses the current
   x coordinate and the new vertical variable t. The parametric
   derivative is evaluated at h, and the resulting continuous
   linear map is evaluated at 1 to recover the real derivative.
   The final function equality uses `iteratedDeriv_succ` for the
   literal h-section. Thus no x derivative is accidentally taken.
   The local transparency option at line 25 addresses elaboration
   of equal scalar-module instances; it adds no axiom or proof
   bypass. Ordinary kernel checking and the axiom reports remain
   in force.

3. Lines 59–65 compose the joint derivative with x -> (x,0) and
   divide by the constant factorial, giving the exact coefficient's
   analytic regularity. Order `⊤` here is the pinned analytic omega,
   as in the independently reviewed implicit-phase chain. It is
   stronger than the manuscript's required smooth regularity.

4. Lines 69–85 choose delta=epsilon/2 **before** choosing p.
   The compact rectangle `[0,L] x [-delta,delta]` lies inside the
   given open analytic rectangle; both x endpoints and both signs
   of h are covered. For each p, lines 87–94 bound the actual
   (p+1)-st vertical derivative on this same compact rectangle and
   choose `Cp=max(M,1)/(p+1)!>0`. Cp depends on p and the fixed
   function, not on x or h. The theorem quantifier order agrees
   exactly with the lock.

5. Lines 97–118 handle h=0 directly. When h!=0, the unoriented
   segment from 0 to h lies in `[-delta,delta]`, so the scalar
   Lagrange remainder applies for either sign. The within-interval
   derivatives in its Taylor polynomial are converted to ordinary
   iterated derivatives at zero using actual local analytic
   regularity and unique differentiability of the nondegenerate
   segment. This supplies the same coefficient definition, even
   though zero is an endpoint of that segment.

6. Lines 119–131 place the Lagrange point in the same compact box,
   use the uniform derivative bound, and take absolute values.
   The result is exactly `Cp*|h|^(p+1)`, with positive factorial
   denominator and no extra x-, j-, n-, or exponential factor.
   The p=0 case is included and uses the first derivative bound;
   no truncation-order restriction or shrinking sequence of
   neighborhoods is hidden in the proof.

7. `ImplicitTaylor.lean:18–19` defines precisely the manuscript
   family for `F(x,h)=symbol m (Y(x,h))`. The public theorem at
   lines 23–42 chooses r,epsilon,C,delta,Y once, retains all five
   original implicit-phase conclusions, then quantifies all k
   for coefficient regularity and all p for Taylor estimates.
   Its zeroth coefficient equals the original symbol throughout
   the open x-neighborhood. The actual implicit equation and
   uniqueness are retained for this same Y, so subsequent grid
   identification can use them without selecting a different Y.

8. Lines 43–63 instantiate every generic assumption: the previously
   constructed actual Y supplies analytic regularity, the literal
   sine-power symbol is globally analytic, and composition supplies
   F. The h=0 identity gives d0=g. The final conversion unfolds
   only the two equal coefficient definitions and F; it does not
   change a bound, denominator, exponent, or domain.

## Trust, independence and limits

Static project-import closure scans cover one file for ParametricTaylor
and 15 for ImplicitTaylor, including each reviewed root module. They
contain no `sorry`, `admit`, custom `axiom`, `unsafe`, or `native_decide`
marker; Challenge is not imported. No new numerical certificate is
introduced. This report independently reviews the two named modules,
their literal definitions and their uses of the previously reviewed
implicit-phase API; it does not claim an independent review of this
reviewer's own source elsewhere in the project.

The coefficient vanishing estimates, extension independence, actual
eigenvalue comparison, low-index estimates, and final target assembly
remain necessary. In particular this theorem alone gives no uniform
critical-order bound for all eigenvalues. No completed-target count
changes. No material correctness or source-fidelity issue was found.
