# Statement lock: actual implicit-grid identification and symbol error

Locked before source on 20 September 2026. This supplies the remaining
identification in (19) and the exponential form of (25), using the same
actual Y and exact coefficient family already constructed. The original
symbol, phase, mesh, spectrum, and manuscript remain unchanged.

Use the existing `mesh n j = j*pi/(n+2)` and the positive step
`h_n=1/(n+2)`. For fixed Y and the already proved uniqueness conclusion
on `(-r/2,pi+r/2) × (-epsilon,epsilon)`, prove that any
`y in [0,pi]` with `F_n(y)=j*pi` equals `Y(mesh n j,h_n)` whenever
`j<=n` and `h_n<epsilon`. All rectangle/interval membership and the
equivalent actual implicit equation must be proved, not assumed.

The fixed-Y public theorem, for m>=2 and that same proved uniqueness
interface, must have constants N,J>=1 and C,c>0 independent of n,j.
For every n>=N and J<=j<=n it supplies an actual angle theta and proves:

* theta and `Y(mesh n j,h_n)` belong to (0,pi);
* `symbol m theta=eigenvalue m n j` with the original one-based index;
* `|theta-Y(mesh n j,h_n)| <= C*exp(-c*j)/(n+2)`;
* both theta and `Y(mesh n j,h_n)` are at most `C*j/(n+2)`;
* the actual symbol error satisfies

  ```
  |eigenvalue m n j - symbol m (Y(mesh n j,h_n))|
    <= C * h_n^(2*m) * j^(2*m-1) * exp(-c*j).
  ```

No displacement estimate, symbol derivative bound, phase solution,
index identification, or error estimate is a premise of this theorem.
They are derived from the already proved actual PhaseQuantitative
result and the actual symbol. The uniqueness interface is a proved
property of the constructed shared Y, not a replacement hypothesis
for the final actual theorem.

The small symbolic component `SymbolDerivative.lean` proves the actual
derivative formula

```
g'(t) = (2*m) * (2*sin(t/2))^(2*m-1) * cos(t/2)
```

and `|g'(t)| <= (2*m)*t^(2*m-1)` for t>=0. Its convex-interval
mean-value consequence is

```
|g(a)-g(b)| <= (2*m)*T^(2*m-1)*|a-b|
```

for a,b in [0,T]. These conclusions use the exact `symbol`, ordinary
derivative rules, `|sin t|<=|t|`, and `|cos t|<=1`; no numerical
certificate or external derivative estimate is needed.

Apply this with `T=C0*j/(n+2)` from the actual quantitative preimage
theorem. The derivative contributes `h_n^(2*m-1)*j^(2*m-1)` and the
angle error contributes `h_n*exp(-c*j)`. Prove the exponent identity
`2*m-1+1=2*m` from m>=2, and enlarge the one constant C to cover all
angle and symbol bounds. The full exponential factor is retained.

An actual existence wrapper will take the one Y furnished by
`manuscript_uniform_implicit_taylor_with_vanishing`, discharge its
fixed-Y uniqueness premise, and retain the same Y and coefficients
along with its analytic regularity, exact derivative/factorial
definition, all-order uniform Taylor remainder, and vanishing bounds.
It adds the displayed eventual spectral error, without assembling the
low-index estimates or the final UniformBound/BulkBound target.

Extension independence of the coefficients remains a separate pending
obligation. No full MF-21 or Comparator claim is made. Source authors
run no compiler; the coordinator retains exact source-matched serial
local test evidence.
