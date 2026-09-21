# Small remainder in high phase windows

Locked on 20 September 2026 before `SpectralWindowBounds.lean`.
This is the quantitative first paragraph of the proof of Lemma 4.

Use the actual functions `manuscriptPhaseFn` and `manuscriptError`, not
abstract functions with a smallness hypothesis. For every m>=2 prove

```
exists J : Nat, 1 <= J and
  forall n : Nat, forall theta in [0,pi],
    (J:Real)*pi-pi/4 <= manuscriptPhaseFn m n theta ->
      |manuscriptError m n hm theta| < 1/4 and
      |deriv (manuscriptError m n hm) theta| < (n+2)/8.
```

The same integer J must work for every n and theta. The source only needs
sufficiently large n, but this estimate follows for all n (the high-phase
range may be empty for small n). It requires no root existence assumption.

The symbolic reduction is `n*theta = F_n(theta)+eta(theta)-2*theta`.
The already proved compact bound on eta therefore gives
`n*theta >= J*pi-pi/4-B-2*pi` in the specified range. Choose a real L
with `C*exp(-c*L)<1/8` from the actual exponential-bound constants and
then choose J so this lower bound exceeds L. The derivative estimate
uses `(n+1)/8 < (n+2)/8`. No interval grid, increasing numerical precision,
or independent derivative bound is introduced.

This theorem is a concrete estimate toward root-window existence and
uniqueness. It does not yet locate or count eigenvalues, identify their
indices, construct Y, or establish MF-21.
