# MF-21: independent audit of the trace obstruction

Date: 19 September 2026. Reviewer: independent Codex subagent `/root/trace_audit`.

This is an informal mathematical audit, not human peer review or a Lean certificate. I read the applicable root `AGENTS.md`; no problem number, target, registry entry, or canonical source was changed.

## Input and verdict

I checked Section 5, equations (26)–(33), of the working-tree manuscript, independently recomputed its identities, and opened the cited primary papers. Input SHA-256 values before any revision:

| File | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-21/solution.md` | `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa` |
| `matrix-functions-and-stability/MF-21/solution.tex` | `1baff64e748b8a3a31d53f1727560937e5c84524a202a25bc92c081b4f1fcd49` |
| `matrix-functions-and-stability/MF-21/solution.pdf` | `829d4e48d9ff61869465faf0470f9ff51f50beeee4fab5d46b191c5c4b9a3c8e` |

**Verdict for Section 5: mathematically valid, conditional only on its explicitly cited classical inverse-kernel theorem and the coefficient construction and interlacing estimate established earlier in the manuscript.** Equation (25) alone supplies no lower bound. Equations (26)–(33) supply a separate contradiction and do establish that the constructed coefficient family cannot attain a uniform remainder of order `h^(2m+1)`.

The stronger assertion excluding *every* continuous coefficient family additionally requires coefficient uniqueness. That short step is absent from the audited Section 5 and is being audited separately. It must be stated before interpreting the conclusion as exclusion of all alternative coefficient families.

## Primary-source checks

[Böttcher–Widom, arXiv:math/0412269](https://arxiv.org/pdf/math/0412269), printed p. 2, formula (5), gives the displayed Green kernel and its reflection symmetry. Printed p. 4, in the paragraph immediately before (13), explicitly states the scaled inverse-kernel convergence in `L∞([0,1]^2)` for multiplier `b=1`; the ceiling-index convention is defined with (11) on p. 3. This is the stronger kernel statement actually needed. It is not merely the operator-norm assertion (12). The source attributes the `b=1` result to earlier work; that attribution should be retained.

[Barrera–Böttcher–Grudsky–Maximenko, arXiv:1710.05243](https://arxiv.org/pdf/1710.05243), printed p. 26, Conjecture 8.4, has the same symbol, grid, threshold, and suggested logarithmic-square cutoff. Proposition 4.2 on p. 12 proves uniqueness for continuous expansion coefficients on an asymptotically dense sampling set. Proposition 8.1 on pp. 24–25 uses that uniqueness for the `m=2` obstruction. Remark 8.3 explicitly distinguishes failure for the constructed coefficients from failure for every continuous choice.

The reference supplied in Sergei Grudsky's email is real and publicly accessible: [Bogoya–Grudsky, *Computational Mathematics and Mathematical Physics* 65 (2025), 1453–1471](https://www.math.cinvestav.mx/~grudsky/Papers/162.pdf), DOI [10.1134/S0965542525700745](https://doi.org/10.1134/S0965542525700745). Its Theorems 2.1–2.2, p. 1457, treat local expansions near nondegenerate simple points; its determinant proof selects two dominant terms. This supports the requested method attribution. The bulk-audit report handles the exact relation to the endpoint-uniform estimates here; I do not certify those estimates as immediate consequences of this reference.

## Detailed verification of Section 5

Write `s=2m`, `h=(n+2)^(-1)`, and `a=(m-1)/2`.

### Positivity and inverse existence

The earlier quadratic-form argument gives `0 < λ_(n,j) < 4^m`. In particular every inverse and inverse eigenvalue used in Section 5 exists and is positive. No assertion about the existence of the limiting differential-operator eigenvalues is needed for the written contradiction.

### Kernel normalization and restriction to the diagonal

Define the step kernel

```math
K_n(x,y)=n^{1-s}(A_n^{-1})_{i_n(x),i_n(y)},
\qquad i_n(x)=\max(1,\lceil nx\rceil).
```

The cited convergence says `ε_n = ||K_n−G_m||_∞ → 0`, with essential supremum. Restricting an arbitrary almost-everywhere statement to a diagonal would be invalid. Here it is justified: on the interior of each grid square, `K_n` is constant; a full-measure subset is dense there; continuity of `G_m` extends the bound to the square's closure. Each diagonal point can use the closure of its assigned grid square. Consequently `|K_n(x,x)−G_m(x,x)|≤ε_n` on the diagonal as well. Endpoint choices are harmless.

Directly integrating the step function gives

```math
\int_0^1 K_n(x,x)\,dx=n^{-s}\operatorname{tr}(A_n^{-1}).
```

Multiplying by `(n/(n+2))^s → 1` gives the manuscript's `h^s` normalization. This does not invoke any generally false continuity of trace under operator-norm convergence.

### Diagonal integral

For `x≥1/2`, use `u=1−x/t`, so `t=x/(1−u)`, `dt=x(1−u)^(-2)du`, and

```math
\frac{(t-x)^{s-2}}{t^s}\,dt=x^{-1}u^{s-2}\,du.
```

The limits are `u=0` and `u=1−x`. Including the prefactor `x^s/((m−1)!)²` gives

```math
G_m(x,x)=\frac{x^{s-1}(1-x)^{s-1}}{(s-1)((m-1)!)^2}.
```

Reflection gives the other half of the interval; continuity includes its endpoints. The beta integral is

```math
\int_0^1 x^{s-1}(1-x)^{s-1}\,dx
=\frac{((s-1)!)^2}{(2s-1)!}.
```

Thus the actual trace limit is the positive rational number

```math
C_m=\frac{((2m-1)!)^2}{(4m-1)!(2m-1)((m-1)!)^2}.
```

All powers, factorials, and shifts in (28)–(29) are correct.

### Hypothetical fixed-index limits

Assume the claimed `h^(s+1)` estimate held for all indices with the constructed coefficients. The uniform Taylor remainder in (23) then gives `λ_(n,j)=g(Y(πjh,h))+O(h^(s+1))` for each fixed `j`. Smoothness and the implicit equation imply `Y→0` and

```math
\frac{Y(\pi jh,h)}h=\pi j+\eta(Y(\pi jh,h))
\longrightarrow \pi(j+a).
```

Since `g(t)/t^s→1`, the limit of `λ_(n,j)/h^s` is

```math
b_j=\pi^s(j+a)^s>0.
```

The positive sign is needed when taking reciprocals and is satisfied for every permitted `m,j`.

### Domination

For `j≥2`, equation (22) gives, uniformly in `n≥j`,

```math
0<\frac{h^s}{\lambda_{n,j}}
\le\left(\frac{3(n+2m)}{4(n+2)j}\right)^s
\le\left(\frac{3m}{4}\right)^s j^{-s}.
```

The last inequality follows from `n+2m≤m(n+2)`. For `j>n`, extend the summands by zero. For `j=1`, the assumed positive limit `b_1` gives an eventual bound, for example `2/b_1`. Discarding finitely many `n` is legitimate for a limit. This supplies a summable majorant because `s=2m>1`. Dominated convergence for counting measure is therefore valid and yields

```math
B_m=\pi^{-2m}\sum_{j=1}^{\infty}(j+a)^{-2m}
```

as the hypothetical trace limit. There is no uncontrolled exchange of an infinite sum and a limit.

### Irrationality and the contradiction

If `m=2r+1≥3`, `a=r` and the series is `ζ(2m)−Σ_(ℓ=1)^r ℓ^(-2m)`. If `m=2r≥4`, it is `(2^(2m)−1)ζ(2m)−Σ_(ℓ=0)^(r−1)(ℓ+1/2)^(-2m)`. Both index ranges in the manuscript are correct. In both cases the subtracted finite sum is a strictly positive rational number.

Euler's even-zeta identity implies `B_m=u−v/π^(2m)` with rational `u,v` and `v>0`. If `B_m` were rational, then `π^(2m)=v/(u−B_m)` would be rational; its denominator cannot be zero because `v>0`. That would make `π` algebraic, contradicting its transcendence. Thus `B_m` is irrational, whereas `C_m` is rational. Uniqueness of limits gives the contradiction.

The argument excludes the global `O(h^(2m+1))` remainder without claiming that (25) is itself a lower bound.

## Optional strengthening: a sharp lower bound for the maximum error

The same ingredients prove more than the manuscript states and can directly address the email's upper-bound concern. There exist a finite integer `J≥1`, a constant `c>0`, and `N` such that

```math
\max_{1\le j\le J}|R_{2m,n,j}|\ge c h^{2m}
\qquad(n\ge N).
```

Here is a complete argument, independent of the hypothetical uniform-error assumption. Put `q_(n,j)=λ_(n,j)/h^s` and retain `b_j=π^s(j+a)^s`. The established trace limit is `Σ_(j=1)^n q_(n,j)^(-1)→C_m`. The comparison series sums to `B_m≠C_m`; let `δ=|C_m−B_m|>0`.

The preceding `j≥2` majorant lets us choose a fixed `J≥1` so that the actual inverse tail, uniformly in `n`, is less than `δ/8`; choose `J` also so the comparison inverse tail is less than `δ/8`. For all sufficiently large `n≥J`, the actual trace is within `δ/8` of `C_m`.

Take a positive `ε` with `ε≤b_1/2` and `2Jε/b_1²≤δ/8`. If every `j≤J` satisfied `|q_(n,j)−b_j|≤ε`, then `q_(n,j)≥b_j/2` and

```math
|q_{n,j}^{-1}-b_j^{-1}|
=\frac{|q_{n,j}-b_j|}{q_{n,j}b_j}
\le\frac{2\varepsilon}{b_1^2}.
```

The difference between the finite reciprocal sums would be at most `δ/8`. Adding that difference, the two tails, and the trace-limit error would imply `δ≤δ/2`, a contradiction. Thus `max_(j≤J)|q_(n,j)−b_j|>ε` for every sufficiently large `n`.

Let `P_(n,j)=Σ_(k=0)^s d_k(πjh)h^k`. The coefficient construction and its Taylor estimate, without any assumption on `λ`, give `P_(n,j)/h^s→b_j` for each fixed `j`. Over the finite set `j≤J`, the error is eventually below `ε/2`. Hence `max_(j≤J)|λ_(n,j)−P_(n,j)|≥(ε/2)h^s`, as claimed.

Combining this with the manuscript's global upper bound (and the bounded `d_(2m)` term) gives an eventual two-sided bound `c h^(2m)≤max_(1≤j≤n)|R_(2m,n,j)|≤C h^(2m)`. It does not identify one particular index that attains a lower bound for every `n`; that stronger claim is unnecessary.

## Limits of this audit

This report validates the trace argument for the stated manuscript snapshot, not the content of an earlier or different PDF, not priority, and not the completion of a formal proof. A Lean proof must either formalize the cited kernel theorem and subsequent analytic steps, or visibly expose them as assumptions; merely proving the final contradiction from those assumptions is not full verification of MF-21.
