# Quantitative actual eigenangles and exact phase preimages

Locked 20 September 2026 before `MF21Restart/PhaseQuantitative.lean`.
This component proves manuscript Lemma 4, equation (19), with the exact
phase preimage y characterized by `F_n(y)=j*pi`. The separate implicit
function construction will later identify this y with `Y(x_(n,j),h)`.

The public theorem is `eigenvalue_eventual_quantitative_phase_preimage`:

```
∀ (m : ℕ) (hm : 2 ≤ m),
  ∃ (N J : ℕ) (C c : ℝ),
    1 ≤ N ∧ 1 ≤ J ∧ 0 < C ∧ 0 < c ∧
    ∀ n : ℕ, N ≤ n → ∀ j : ℕ, J ≤ j → j ≤ n →
      ∃ θ y : ℝ,
        θ ∈ Set.Ioo 0 Real.pi ∧ y ∈ Set.Ioo 0 Real.pi ∧
        symbol m θ = eigenvalue m n j ∧
        manuscriptPhaseFn m n y = (j : ℝ) * Real.pi ∧
        |θ - y| ≤ C * Real.exp (-c * (j : ℝ)) / (n + 2 : ℝ) ∧
        θ ≤ C * (j : ℝ) / (n + 2 : ℝ) ∧
        y ≤ C * (j : ℝ) / (n + 2 : ℝ)
```

The constants depend only on m and work simultaneously for every
sufficiently large matrix size and every original one-based index
J<=j<=n. The largest eigenvalue is included. The theorem makes no
claim for indices below J or for the accessor's totalized values.
Both angles are strictly inside (0,pi).

The theta witness comes from the already proved actual index-to-window
bridge, not an assumed root labeling. Its literal residual is zero.
Jordan's sine inequality on the quarter-period cell and the actual
error estimate yield the phase discrepancy. If `|eta|<=B` and the
actual error constants are c0,C0, then

```
n*theta >= j*pi - (B+9*pi/4),
|E_n(theta)| <= C0*exp(c0*(B+9*pi/4))*exp(-(c0*pi)*j).
```

The exact lower phase derivative `(n+2)/2` bounds the inverse distance
between theta and y. IVT and the exact phase endpoints construct y;
it is not an existential assumed phase solution. Bounded eta and
j>=1 give both size bounds with one enlarged positive constant C.
All derivative, error, root and ordering estimates are discharged
from actual modules. No asymptotic estimate, spectral approximation,
or choice of Y is a public hypothesis.

Only this finite-location component is claimed. The implicit function
Y, Taylor expansion, low-index control, trace obstruction assembly,
and original MF-21 Target remain separate. No new numerical search,
axiom, or literature premise is introduced. The author launches no
compiler; the coordinator owns serialized local checks. This lock
asserts no local or Comparator success.
