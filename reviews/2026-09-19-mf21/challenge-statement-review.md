# MF-21: independent semantic review of the Lean challenge statement

Date: 19 September 2026. Reviewer: independent Codex subagent `/root/trace_audit`.

Reviewed file: [lean/Challenge.lean](lean-development-source.tar.gz).
Reviewed SHA-256: `34835e10fc601004efc13530e3673056345d87bde23d5b176d8e302bf6c548cc`.

**Verdict: the proposed proposition correctly represents the canonical MF-21 target using the explicit signed-binomial Toeplitz matrix.** The still-unproved formal bridge from the source's Fourier definition is openly identified. `FullTarget` is a proposition definition, not a proof of that proposition. This semantic review does not turn it into a theorem.

## Matrix and eigenvalues

The real matrix entry is

```math
(-1)^{|i-j|}\binom{2m}{m+|i-j|}.
```

This is mathematically the correct Toeplitz entry. To verify its relation to
the original symbol informally, put `z=exp(iθ)` and expand

```math
g_m(\theta)=(1-z)^m(1-z^{-1})^m
=(-1)^m z^{-m}(1-z)^{2m}.
```

The coefficient at Laurent exponent `k` is
`(-1)^k binom(2m,m+k)` when `−m≤k≤m`, and zero otherwise. Binomial
symmetry and parity replace `k` by `|k|`. Fourier orthogonality identifies
this Laurent coefficient with the source's Fourier integral. These steps
have not been proved in this Lean file and remain formal obligations,
exactly as its documentation says.

`Nat.dist` correctly encodes `|i−j|`; `Nat.choose` supplies zero beyond the
band. There is no accidental circulant wraparound. Changing matrix indices
from `1,...,n` to `Fin n` leaves their differences unchanged.

The eigenvalue definition uses mathlib's actual Hermitian eigenvalues, not
an arbitrary real sequence or a assumed approximation. I inspected the
pinned mathlib source `Mathlib/Analysis/Matrix/Spectrum.lean` at commit
`0df444a360eaa60ab8c11dca51a86af692955474`. Its
`Matrix.IsHermitian.eigenvalues₀_antitone` establishes decreasing order;
`roots_charpoly_eq_eigenvalues₀` identifies the multiset with all
characteristic-polynomial roots. Reversal by `Fin.rev`, followed by the
cardinality cast, therefore gives increasing eigenvalues with multiplicity.
The source index corresponding to `j : Fin n` is correctly `j.val+1`.

## Quantifiers and regularity

| Requirement | Lean statement | Assessment |
| --- | --- | --- |
| Every integer `m≥3` | `∀ m : ℕ, 3 ≤ m → TargetAt m` | Exact |
| One coefficient family, allowed to depend on `m` | `∃ d` inside `TargetAt m` | Exact |
| Coefficients independent of `n,j` | `d : ℕ → ℝ → ℝ` outside the matrix-size and index quantifiers | Exact |
| Real continuity on `[0,π]` | `ContinuousOn (d k) (Set.Icc 0 Real.pi)` for `k≤2m` | Exact; no extra differentiability required |
| `d_0=g_m` | Equality on the entire closed interval | Exact |
| Sampling point `jπ/(n+2)` | `(j.val+1)*π/((n:ℝ)+2)` | Exact after index conversion |
| Truncation through order `p` | `Finset.range (p+1)` | Includes both `0` and `p` |
| All orders `0≤p≤2m−1` | `∀ p : ℕ, p ≤ 2*m-1 → UniformOrder m p d` | Exact because the enclosing statement has `m≥3` |
| Uniform error constant and eventual threshold | `∃ D>0, ∃ N, ∀ n≥N, ∀ j : Fin n` | Constants cannot depend on `n,j` |
| Natural logarithm, squared, rounded up | `Nat.ceil ((Real.log ((n:ℝ)+2))^2)` | Exact |
| Bulk order `2m` | `cutoff n ≤ j.val+1`, remainder exponent `2m+1` | Exact |
| Failure at order `2m` for the same family | `¬ UniformOrder m (2*m) d` inside the same existential | Exact canonical negative assertion |

Including `n=0` in the ambient natural quantifier is harmless: there is no
`j : Fin 0`, and the eventual threshold can in any event be enlarged to one.
The functions' values outside `[0,π]` and coefficients with `k>2m` have no
effect. Using functions on all reals with `ContinuousOn` on the interval is
equivalent to the intended functions defined only on that interval.

## Separate stronger obstruction

`UniversalObstruction` correctly states that no continuous coefficient
family gives a uniform order-`2m` expansion. It deliberately does not assume
the leading coefficient equality, making the stronger formulation explicit.
It is not silently substituted for the canonical same-family claim.

The informal uniqueness supplement proves the bridge: bulk existence plus
coefficient uniqueness makes any hypothetical global family equal to the
constructed family, including its leading coefficient. Neither this
implication nor either challenge proposition is proved merely by defining
the propositions.

## Remaining boundary

The file's symmetry theorem permits use of the library spectral theorem.
It does not prove asymptotics, coefficient existence, the endpoint
obstruction, or the Fourier-coefficient bridge. A successful compilation
checks that the proposition and symmetry proof are well formed. It does
not establish `FullTarget` or `UniversalObstruction`.

No canonical source or problem registry was modified during this review.
