# MF-21: coefficient uniqueness and the scope of the obstruction

19 September 2026. Technical supplement by Codex. This is an informal proof,
not a certificate that the full Toeplitz theorem has been verified in Lean.
The published manuscript and original problem statement are retained unchanged.

## Coefficient uniqueness

Fix a nonnegative integer $p$, put $h_n=(n+2)^{-1}$, and let
$L_n=\lceil(\log(n+2))^2\rceil$. Suppose two families
$d_0,\ldots,d_p$ and $e_0,\ldots,e_p$ are continuous on $[0,\pi]$ and,
for the same numbers $\lambda_{n,j}$, each satisfies

$$
\left|\lambda_{n,j}-\sum_{k=0}^p c_k(j\pi h_n)h_n^k\right|
\le C_c h_n^{p+1}
\qquad(n\ge N_c,\ L_n\le j\le n),
$$

where $c=d$ or $c=e$. Then $d_k=e_k$ on $[0,\pi]$ for every $0\le k\le p$.

**Proof.** Fix $x\in(0,\pi)$ and set
$j_n=\lfloor x(n+2)/\pi\rfloor$. Since
$j_n/(n+2)\to x/\pi\in(0,1)$ and
$L_n/(n+2)\to0$, eventually $L_n\le j_n\le n$ and $j_n\ge1$.
The sampling points $x_n=j_n\pi h_n$ belong to $[0,\pi]$ and tend to $x$.
Subtracting the two estimates gives

$$
\left|\sum_{\ell=0}^p(d_\ell-e_\ell)(x_n)h_n^\ell\right|
\le (C_d+C_e)h_n^{p+1}.
$$

We induct on $k$, proving equality on the entire closed interval at each
step. Assuming equality for every $\ell<k$, division by $h_n^k>0$ yields

$$
\left|(d_k-e_k)(x_n)+
\sum_{\ell=k+1}^p(d_\ell-e_\ell)(x_n)h_n^{\ell-k}\right|
\le(C_d+C_e)h_n^{p+1-k}.
$$

All higher coefficients are bounded on the compact interval. Therefore the
finite sum tends to zero, as does the right-hand side, because $k\le p$.
Continuity gives $d_k(x)=e_k(x)$. This holds for every interior $x$;
continuity extends equality to both endpoints. This also establishes the
base case $k=0$, where there are no lower coefficients. Induction proves
the assertion. $\square$

This is the specialization of the uniqueness principle already proved in
[Barrera–Böttcher–Grudsky–Maximenko, Proposition 4.2](https://arxiv.org/pdf/1710.05243).
That paper's Remark 8.3 also distinguishes failure for a specified coefficient
family from failure for every continuous family. The elementary proof here
spells out the logarithmic-square cutoff and requires only the highest-order
estimate, rather than assuming all lower truncation estimates separately.

## Application to the manuscript

Apply the lemma with $p=2m$ to the coefficients constructed in equations
(3)–(5) and any hypothetical continuous family admitting a uniform
$O(h_n^{2m+1})$ expansion for all $1\le j\le n$. The hypothetical family
also satisfies that estimate on $j\ge L_n$, so it must coincide with the
constructed family, including at the endpoints. Consequently the trace
contradiction in equations (26)–(33) rules out the hypothetical family.

This supplies the omitted justification needed for the stronger interpretation
that no continuous coefficient family can achieve that uniform order. The
canonical three-part statement already specifies that the same constructed
coefficients are used throughout; the manuscript's Section 5 addresses that
statement directly. No conjecture, eigenvalue grid, cutoff, or permanent ID
is altered by adding the uniqueness explanation.

## What equation (25) does and does not prove

The estimate $|R|\le C h_n^{2m}$ does not imply failure of
$R=O(h_n^{2m+1})$. The current seven-page PDF does not use it for that
inference: its obstruction is the distinct trace calculation in Section 5.
The [independent trace audit](trace-audit.md) checks that calculation and
gives a stronger consequence of the same inputs:

$$
\exists J\ge1,\ c>0,\ N:\quad
\max_{1\le j\le J}|R_{2m,n,j}|\ge c h_n^{2m}
\quad(n\ge N).
$$

Together with the global upper bound this gives an eventual two-sided
bound of order $h_n^{2m}$ for the maximal error. It does not claim that a
specified individual eigenvalue has that error for every large $n$.

## Method attribution

The simple-loop method should be credited explicitly to its developers.
The additional reference supplied in the correspondence is
M. Bogoya and S. Grudsky, *Eigenvalues of non-Hermitian banded Toeplitz
matrices approaching simple points of the limiting set*, Computational
Mathematics and Mathematical Physics **65** (2025), 1453–1471,
[DOI](https://doi.org/10.1134/S0965542525700745),
[author-hosted paper](https://www.math.cinvestav.mx/~grudsky/Papers/162.pdf).
Its Theorems 2.1–2.2 treat local phase equations and expansions near
nondegenerate simple points. A precise comparison of endpoint-dependent
constants would be required before asserting that it directly gives the
manuscript's shrinking cutoff. This audit makes no novelty or priority claim.
