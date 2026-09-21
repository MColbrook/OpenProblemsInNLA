# Phase-window roots: statement lock

Locked before writing `MF21Restart/PhaseWindowRoots.lean`. This component
formalizes manuscript Lemma 4, lines 237–239, through uniqueness of a
simple zero in each high phase window. Existing actual functions and the
published matrix/eigenvalues are unchanged.

For every `m : ℕ` and `hm : 2 ≤ m`, prove the following exact type, where
`F = manuscriptPhaseFn m n` and `H = manuscriptResidual m n hm`:

```
∃ N J : ℕ, 1 ≤ N ∧ 1 ≤ J ∧
  ∀ n : ℕ, N ≤ n → ∀ k : ℕ, J ≤ k → k ≤ n →
    (∃! θ : ℝ,
      θ ∈ Set.Ioo 0 Real.pi ∧
      |manuscriptPhaseFn m n θ - (k : ℝ) * Real.pi| ≤ Real.pi / 4 ∧
      manuscriptResidual m n hm θ = 0) ∧
    ∀ θ : ℝ, θ ∈ Set.Ioo 0 Real.pi →
      |manuscriptPhaseFn m n θ - (k : ℝ) * Real.pi| ≤ Real.pi / 4 →
      deriv (manuscriptResidual m n hm) θ ≠ 0
```

The second conclusion is the derivative sign argument on the entire
closed phase window, so in particular the unique zero is simple. The
same `N,J` must work for every indicated `n,k`; no error, derivative,
monotonicity, or root-existence estimate occurs in the public premises.

The window includes its phase endpoints `k*pi ± pi/4`, while theta is
strictly between `0` and `pi`. The actual endpoint values
`F(0)=-(m-1)*pi/2` and `F(pi)=(n+1)*pi`, together with `1≤k≤n`, place
both window endpoints strictly inside that theta interval. Continuity
and strict monotonicity of `F` must construct their preimages.

The proof uses the already established actual eventual lower bound
`F' >= (n+2)/2` and the actual uniform high-phase bounds
`|E|<1/4`, `|E'|<(n+2)/8`. Set
`R(θ)=(-1)^k*(sin(F(θ))+E(θ))`. The exact shift identities rewrite its
sine and cosine in terms of `F(θ)-k*pi`. The existing kernel-mode
certificate `phase_window_margin` gives `sin(pi/4)>1/4`; the exact
identity `cos(pi/4)=sin(pi/4)` gives the same margin for cosine on the
whole window. Thus `R` has negative and positive endpoint values and a
strictly positive derivative throughout the window. IVT and strict
monotonicity prove existence and uniqueness. No new numeric certificate,
grid, root finder, or assumed determinant identity is introduced.

Private scalar helpers may state the calculus argument with arbitrary
real `F,E` and their explicit derivative/smallness assumptions, but the
public theorem must discharge every such assumption with the actual
functions. This component does not exclude gaps or the final window at
`(n+1)*pi`, identify the original eigenvalue index with `k`, construct
`Y`, or prove MF-21. Compiler execution remains with the coordinator;
this lock makes no build or Comparator claim.
