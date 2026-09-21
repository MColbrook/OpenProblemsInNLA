# Final phase window: statement lock

This lock precedes `MF21Restart/FinalPhaseWindow.lean` and formalizes
the final-window argument in manuscript Lemma 4, lines 241–247.
All phase, error, and residual functions remain the actual existing ones.

For every `m : ℕ` and `hm : 2 ≤ m`, prove these two conclusions:

```
∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
  ∀ θ : ℝ, θ ∈ Set.Icc 0 Real.pi →
    |manuscriptPhaseFn m n θ - (n + 1 : ℝ) * Real.pi| ≤ Real.pi / 4 →
    Real.pi / 2 ≤ θ
```

and

```
∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
  ∀ θ : ℝ, θ ∈ Set.Ioo 0 Real.pi →
    |manuscriptPhaseFn m n θ - (n + 1 : ℝ) * Real.pi| ≤ Real.pi / 4 →
    Real.pi / 2 ≤ θ ∧ manuscriptResidual m n hm θ ≠ 0
```

The thresholds depend only on `m`. No independent phase, error,
monotonicity, or exponential estimate is assumed in these public
statements. There is no phase-label threshold `J` in this component.
The geometric upper-half statement includes `θ=π`; the nonzero residual
statement excludes it, as required by the actual artificial zero there.
The phase window itself is closed, so its lower phase endpoint is included.

The geometry follows from boundedness of the actual `eta`, the defining
identity `F=(n+2)*θ-eta`, and the lower phase-window bound. For large
`n`, any point of this final window must have `θ≥π/2`.

The existing actual derivative lower bound and the mean value theorem
give

```
((n+2)/2)*(pi-theta) <= F(pi)-F(theta).
```

Jordan's inequality `2*|x|/pi <= |sin x|` on `|x|<=pi/2`, with
`x=F(theta)-(n+1)*pi`, and the exact sine shift identity then give

```
((n+2)/pi)*(pi-theta) <= |sin(F(theta))|.
```

This is the elementary sine lower bound requested by the manuscript;
it needs no additional numeric certificate. The actual endpoint estimate
(12) bounds `|E|` by
`C*(n+1)*(pi-theta)*exp(-c*n*pi/2)`. Since `c>0`, choose one threshold
with `C*exp(-c*n*pi/2)<1/pi` for every larger `n`. For `theta<pi`,
the strictly positive factor `pi-theta` shows `|E|<|sin(F)|`, hence the
actual residual cannot vanish. The proof must not cancel this factor at
`theta=pi` or assert endpoint nonvanishing.

Private scalar limit or derivative helpers may be used, but their
hypotheses must be discharged by the existing actual theorems. No new
axioms, external dependency, root-finding computation, full gap exclusion,
eigenvalue index identification, or MF-21 completion is part of this
component. No compiler is run by its author; the coordinator owns local
testing. This lock makes no compilation or Comparator claim.
