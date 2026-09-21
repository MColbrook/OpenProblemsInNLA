# High-phase root coverage: statement lock

This lock precedes `MF21Restart/PhaseRootCoverage.lean`. It formalizes
the exclusion of gaps and roots above the listed ordinary windows in
manuscript Lemma 4, lines 241–249, using the separately proved final-window
exclusion. The actual phase and residual functions remain unchanged.

For every `m : ℕ` and `hm : 2 ≤ m`, prove exactly:

```
∃ N J : ℕ, 1 ≤ N ∧ 1 ≤ J ∧
  ∀ n : ℕ, N ≤ n → ∀ θ : ℝ, θ ∈ Set.Ioo 0 Real.pi →
    (J : ℝ) * Real.pi - Real.pi / 4 ≤ manuscriptPhaseFn m n θ →
    manuscriptResidual m n hm θ = 0 →
    ∃ k : ℕ, J ≤ k ∧ k ≤ n ∧
      |manuscriptPhaseFn m n θ - (k : ℝ) * Real.pi| ≤ Real.pi / 4
```

The same two thresholds work for all `n,theta`. All derivative,
monotonicity, error, and endpoint estimates must be discharged by actual
theorems; none is a public premise. The high-phase threshold and the
ordinary phase windows are closed. Theta itself is strictly between
zero and pi.

The exact nearest label is the natural floor of `F(theta)/pi+1/2`.
The lower high-phase bound makes the floor argument nonnegative and
forces `k>=J`. Eventual actual phase monotonicity and
`F(pi)=(n+1)*pi` force `k<=n+1`. The floor inequalities give a distance
at most `pi/2` from `k*pi`; this is an exact order argument, not a
floating-point nearest-integer procedure.

At a residual zero the actual error bound gives `|sin F|=|E|<1/4`.
The sine shift identity, monotonicity on the half-period, and the
existing certified `sin(pi/4)>1/4` margin force the nearest distance
to be at most `pi/4`. The proved final-window exclusion rules out
`k=n+1`, leaving `J<=k<=n`.

This component does not define a root-choice function, identify the
phase label with the original eigenvalue index, count roots below the
high-phase range, or complete the MF-21 target. It introduces no axiom,
new numerical certificate, altered phase branch, or unproved spectral
premise. Compiler execution remains with the coordinator; this lock
claims neither a local test nor Comparator success.
