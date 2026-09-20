# Quantization and expansion proof audit

This note records the formal components added on 20 September 2026 in the local review worktree. It does not change the historical audit or claim that the repository's full Lean acceptance protocol has been completed.

`MF21Quantization.model_exists m hm` constructs a model for every `m > 0` from the actual root-defined phase extension proved in `BulkEta.lean`. There is no assumed implicit inverse, assumed Taylor estimate, or assumed eigenvalue expansion in that theorem.

The construction uses the source convention

\[
\eta(\theta)=\theta+2\psi(\theta),\qquad
Y(s,h)-h\eta(Y(s,h))=s.
\]

For `h=1/(n+2)` and `s=j*pi*h`, this is exactly `(n+1)*Y-2*psi(Y)=j*pi`. The phase endpoint is `eta(0)=(m-1)*pi/2`, giving the shifted fixed-index profile `((j+(m-1)/2)*pi)^(2*m)` for one-based source indices.

The checked proof proceeds as follows:

- `UniformQuantization.lean` defines one interval inverse with `Function.invFunOn`. Compact bounds on the phase and its derivative give existence by the intermediate value theorem and injectivity by strict monotonicity. The actual interval inverse agrees locally with the smooth implicit-function branch, including at all edges of the compact parameter rectangle. The same proof gives inverse stability with constant two and preserves order.
- `UniformTaylor.lean` defines one coefficient family by vertical derivatives divided by factorials. Evaluation of derivative tensors proves that each coefficient is smooth at every point of the closed source interval. A compact bound on the next derivative gives a uniform Taylor remainder at every finite order. The coefficient family does not change with the requested truncation order.
- `QuantizationTaylor.lean` applies these results to the actual symbol and phase. The zeroth coefficient is the source symbol. Along a fixed-index ray `s=c*h`, the implicit equation implies `Y/h -> c+eta(0)`; the sine/sinc factorization then proves the exact scaled symbol limit. The uniform Taylor estimate transfers this limit to the order-`2*m` approximant.
- `SymbolTransfer.lean` proves the actual grid inverse lies in `(0,pi)`. The elementary power-difference inequality and the sine Lipschitz bound give the sharp factor `max(theta,Y)^(2*m-1)` in the symbol error. Thus exponential angle error and the linear angle bound imply the required `h^(2*m)` symbol error.
- `ExponentialCutoff.lean` bounds polynomial times exponential decay using the exponential series. It proves the exact natural-log-squared cutoff gains one further factor `1/(n+2)` uniformly above the cutoff.
- `FiniteHeadModel.lean` controls all initial indices below a fixed cutoff using the actual circulant eigenvalue upper bound and inverse stability against the angle zero. This avoids any need for separate endpoint-vanishing formulas for individual coefficients.
- `ExpansionEstimates.lean` combines the head and tail bounds with the common Taylor family. Its theorem `expansion_assertions_of_tailAngle` proves the continuity, leading coefficient, every lower uniform order, and the cutoff order-`2*m` estimate. Its sole remaining spectral premise is `TailAngleApproximation`, explicitly defined in `SymbolTransfer.lean` in terms of actual sorted Toeplitz eigenvalues, their actual eigenangles, and the constructed inverse.

The last conditional theorem is not itself the nonexistence assertion or `FullTarget`. The separate actual trace obstruction and the separate actual tail-angle theorem must be combined with it. The conditional premise has not been hidden in a definition of the coefficients or supplied as an axiom.

All eight modules were checked locally with Lean 4.33.1 and `--trust=0`. Printed proof closures use only `propext`, `Classical.choice`, and `Quot.sound`. Exact source and raw-output hashes are in `lean/verification/quantization-expansion-raw-result.json`. These checks used cached pinned mathlib dependencies on macOS; they are not the required independent pinned Linux Comparator run.

The subsequent frozen `FinalTarget.lean` now combines the unconditional actual tail-angle theorem and actual trace obstruction with these estimates. `MF21Verified.fullTarget` and `universalObstruction` have passed local `--trust=0` checks; `smooth_common_family` additionally selects the same family for all expansion estimates, smoothness, and matching finite-head/global error bounds. See `lean/verification/final-target-raw-result.json` and the separately labeled final semantic author review. The repository's independent Linux acceptance gate remains separate.
