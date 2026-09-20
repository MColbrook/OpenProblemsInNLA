# MF-21: independent audit of Sections 1–4

Date: 19 September 2026. Reviewer: separate Codex agent /root/bulk_audit.

Reviewed files: matrix-functions-and-stability/MF-21/solution.md, SHA-256
6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa, and its
solution.tex, SHA-256
1baff64e748b8a3a31d53f1727560937e5c84524a202a25bc92c081b4f1fcd49.
Repository HEAD: de97a72364055bddb65f23d2da8566e0594b2a8c.
Line references refer to the reviewed Markdown. The root AGENTS.md was read.
No canonical manuscript, problem identity, or registry was changed.

**Scoped verdict:** I found no mathematical error in Sections 1–4 establishing
the global expansion through order $2m-1$ and order $2m$ above the stated
cutoff. In particular the determinant normalization and endpoint counting
withstand the checks below. This is an AI mathematical audit, not a Lean
certificate or human peer review. It does not certify Section 5, coefficient
uniqueness against competing continuous families, or novelty.

## 1. Stable roots and phase: lines 70–110

For $s=2-2\cos\theta>0$, a unit-circle root would give
$2-r-r^{-1}\in[0,4]$, whereas $\omega_\ell s$ is nonreal or strictly
negative. Reciprocity supplies one inside and one outside root. A double
root requires the right side to be $0$ or $4$, both excluded.

The displayed $\kappa_\ell$ satisfies $\kappa_\ell^2=-\omega_\ell$ and
$\Re\kappa_\ell>0$, so the derivative $-\kappa_\ell$ selects the stable
branch. Factoring $\theta$ from the square root of the discriminant supplies
the smooth extension at zero. The function
$-\log|r_\ell(\theta)|/\theta$ has positive limit $\Re\kappa_\ell$ and
is positive on the remaining compact interval. This proves a common
exponential decay constant.

The factors defining the argument have positive real part because
$|r_\ell|<1$. Their quotients by $\theta$ have the nonzero limits
$2\sin(\pi\ell/(2m))e^{i\pi\ell/(2m)}$, giving a smooth endpoint argument
and the stated sum. At $\pi$, conjugate pairing cancels the arguments;
the possible real inside root is positive. Equation (7) is correct.

## 2. Boundary determinant and normalization: lines 142–215

The translated ghost indices are exactly those of (13). Nonzero outside
recurrence coefficients allow unique continuation from $2m$ consecutive
values. Extending a finite eigenvector with zero ghost values consequently
gives a full recurrence solution, and restriction gives the converse.
Restriction is injective because $2m$ consecutive zeros force the recurrence
solution to vanish. This justifies the kernel identification, rather than
merely the implication from an eigenvalue to a determinant zero.

I checked the leading coefficients directly. Conjugate closure of the
stable roots gives
$$
\prod_\ell(1-r_\ell z)=\overline f,\quad
\prod_\ell(q_\ell-z)=Q\overline f,\quad
\prod_\ell(z^{-1}-r_\ell)=z^{-(m-1)}\overline f.
$$
The Laplace signs of the two leading selections are opposite. Including
the bottom-row powers therefore gives
$$
\sigma V(R)V(O)Q^{n+m+1}
\left[z^{n+1}\overline f^{\,2}-z^{-(n+1)}f^2\right].
$$
This is precisely (16): its phase orientation and $n+2$ grid shift are
correct.

For another selection, its root product divided by $Q$ is the product
of selected inside-root factors and reciprocals of omitted outside-root
factors, times factors of modulus one. At least one contracting factor
occurs. This proves (17).

The cancellation at zero has the stated order. The root slopes
$-\kappa_\ell,\kappa_\ell,i,-i$ are distinct. Thus each root difference is
$\theta$ times a smooth nonzero factor at zero. The numerator of $a_S$
has order $2\binom m2=m(m-1)$; its denominator has order
$$
2\binom{m-1}{2}+2(m-1)=m(m-1),
$$
with nonzero leading coefficient. Dividing these powers proves bounded
coefficients and first derivatives. The factor $|f|^2$ is smooth in the
real parameter and leaves a positive factor after dividing by
$\theta^{2m-2}$. At $\pi$ the denominator is nonzero. Differentiating
the finite sum (18) consequently proves (11).

Conjugation swaps the unit-circle columns and induces equal permutations
on the inside and outside lists. Its total sign is minus one. Both
$D_n$ and its normalizer are purely imaginary, so their quotient and
$E_n$ are real. Coincident columns at $\pi$ give $E_n(\pi)=0$.
Integrating (11) proves the stronger bound (12). The endpoint cancellation
is essential and is correctly supplied.

## 3. Root indexing and the circulant: lines 219–277

The quadratic-form argument puts all eigenangles strictly inside
$(0,\pi)$. Choosing fixed large $J$ makes the perturbation and derivative
small throughout the high-phase region. The intervals around $k\pi$,
$J\le k\le n$, each contain exactly one simple zero.

If the boundary matrix had nullity at least two, each term in the
derivative of its determinant would vanish: replacing only one column
cannot restore full rank. This contradicts the simple determinant zero.
Symmetry gives algebraic simplicity of the eigenvalue.

The last interval must exclude the artificial zero at $\pi$. There,
the phase derivative bound gives
$$
|\sin F_n(\theta)|\ge c(n+2)(\pi-\theta).
$$
Equation (12) has the same vanishing factor times an exponentially small
coefficient, so no interior zero occurs. There are no zeros in the
intervening gaps. Hence the upper range has exactly $n-J+1$ simple
eigenangles and none above it. Counting from the top proves the claimed
indices without assuming anything about the lower eigenvalues.

The exact phase root lies inside $(0,\pi)$, since $F_n(0)<0$ and
$F_n(\pi)=(n+1)\pi$. Uniqueness identifies it with $Y$; the mean-value
estimate gives (19).

For $N=n+2m$, no Fourier coefficient wraps into the leading block:
when $|j-k|\le n-1$, a nonzero wrap has absolute index at least
$2m+1>m$. The sorted circulant spectrum has the displayed floor
indexing for both parities of $N$. Interlacing proves (21);
$\lfloor j/2\rfloor\ge j/3$ for integers $j\ge2$ proves (22).

## 4. Uniform expansions: lines 282–308

The implicit-function construction on a compact interval supplies a common
small $h$-interval and uniform Taylor remainders. At $h=0$, the $k$-th
derivative of $g(Y)$ has factors $g^{(s)}(x)$ with $s\le k$,
multiplied by bounded smooth factors. This proves (24). The coefficients
depend only on endpoint jets, so the chosen smooth extension does not
affect them.

For $j\ge J$, the angles in the mean-value theorem are bounded by $Cjh$.
Multiplying (19) by $g'(t)=O(t^{2m-1})$ gives (25). For $j<J$,
interlacing and (24) give $O(h^{2m})$ directly. This proves order
$2m-1$ globally. Removing bounded higher coefficients gives all lower
orders with the same family. Finally,
$j^{2m-1}e^{-cj}\le Ch$ uniformly for $j\ge\log^2(1/h)$ once $h$
is small, proving the claimed order-$2m$ cutoff.

**Equation (25) only supplies an upper bound.** It cannot independently
prove nonexistence or a lower bound. The current source continues through
equations (26)–(33), and its proposed obstruction is the separate trace
argument in Section 5. The email calls (25) the final formula. The coordinating
agent downloaded the public PDF and confirmed that it is byte-identical to
the local seven-page PDF and contains (26)–(33) on pages 6–7. This rules out
a discrepancy between the current public PDF and the source audited here;
it does not establish which version the correspondent read.

## 5. Attribution and limits

The manuscript should credit the simple-loop method and cite
Bogoya–Grudsky, *Eigenvalues of Non-Hermitian Banded Toeplitz Matrices
Approaching Simple Points of the Limiting Set*, **65** (2025), 1453–1471,
[DOI](https://doi.org/10.1134/S0965542525700745),
[author-hosted full paper](https://www.math.cinvestav.mx/~grudsky/Papers/162.pdf).
I read its Sections 1–2. Theorems 2.1–2.2, page 1457, give a phase
equation and all-order expansions near simple nondegenerate points. The
setup fixes a neighborhood of an interior point. A direct deduction of
the shrinking logarithmic-squared cutoff additionally needs control of
constants near the endpoint; that comparison has not been established
here. This audit neither disputes Grudsky's attribution nor claims that
the cutoff is new.

No numerical experiment was a premise. Before claiming the full theorem
verified, incorporate the separate uniqueness and trace audits.
Any Lean claim must distinguish the actual Toeplitz result from an
abstract theorem that assumes the analytic inputs.
