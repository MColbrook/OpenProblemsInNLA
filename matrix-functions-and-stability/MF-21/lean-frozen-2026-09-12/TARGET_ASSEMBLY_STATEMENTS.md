# Final assembly of the unchanged MF21Restart.Target

Locked before TargetProof.lean, 20 September 2026.

The final public declaration will be

    MF21Restart.target_proved : MF21Restart.Target

where Target is the unchanged proposition in Definitions.lean. No
spectral, inverse-kernel, coefficient, interlacing, transcendence, or
trace-limit hypothesis is added to this declaration.

For each m>=3, obtain exactly one Y from
manuscript_implicit_taylor_with_spectral_error, and set
d_k=implicitPhaseCoefficient m Y k. Retain all IFT, uniform Taylor,
vanishing, and actual spectral-error data for that same Y. Derive the
required coefficient continuity and d0=symbol from the actual analytic
coefficient construction.

Apply the fixed-Y expansion assembly. Discharge its finite-prefix
eigenvalue premise with the actual eigenvalue_fixed_prefix_bound from
CirculantBounds. Its bulk proof uses the original logarithmic-squared
cutoff and the actual exponential spectral estimate. This gives all
UniformBound orders p<=2m-1 and BulkBound for the same d.

For the obstruction, suppose UniformBound m d (2*m). The actual
fixed-index bridge, using the uniform IFT displacement and the full
order-2m Taylor sum, gives (30) for every original j>=1. Supply the
Tannery passage's reciprocal majorant using the actual
eigenvalue_eventual_reciprocal_tail_bound from CirculantBounds; do not
assume that majorant or a trace limit. The conditional passage then gives
the irrational series in (31) as the limit of the actual scaled inverse
trace. ActualTraceLimit gives the positive rational constant in (29)
for exactly that same sequence. Uniqueness of real limits and the proved
trace_series_irrational yield a contradiction.

An auxiliary fixed-Y theorem may isolate this last contradiction under
the already constructed IFT/Taylor properties, but it must discharge the
spectral majorant and trace identities internally. The final Target
theorem may have no extra premises. The manuscript, Definitions,
Challenge, Solution, and Comparator metadata are not edited by this
source task. Source existence does not assert a successful Lean run,
independent review, or Comparator run; all remain separately recorded.

## Prior-lock extension: the manuscript's smooth coefficient conclusion

Added before modifying the still-untested TargetProof source. The stronger
public theorem manuscript_smooth_target will state: for each m>=3 there
exists one family d for which every d_k, k<=2m, is ContDiffAt Real infty
at every x in [0,pi], and the same d satisfies d0=symbol, all global
orders through 2m-1, the original bulk order 2m, and failure of the
global critical order. Here infty is smooth order, not top=omega.

Use the already proved analytic regularity hcoeff for the constructed
family and weaken only the regularity order by ContDiffAt.of_le. All
spectral conclusions continue to use exactly that family. Derive
target_proved from manuscript_smooth_target by continuity of the same
d; do not repeat the existential construction or prove a disconnected
smoothness helper. This additional explicit statement preserves the
manuscript Theorem 1 smoothness claim while leaving Target unchanged.
