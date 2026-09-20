# MF-21: independent review of the proposed Lean statement

Date: 19 September 2026. Reviewer: separate Codex agent /root/bulk_audit.

Reviewed file: lean/Challenge.lean, SHA-256
34835e10fc601004efc13530e3673056345d87bde23d5b176d8e302bf6c548cc.
I also inspected the spectral API in the mathlib cache identified by the replay
manifest, at commit 0df444a360eaa60ab8c11dca51a86af692955474.

**Verdict:** the proposed proposition definitions faithfully encode the
canonical continuous-coefficient, three-part target for the explicitly defined
signed-binomial matrix. The eigenvalues are actual library eigenvalues in the
correct increasing order; the grid, cutoff, coefficient family, and quantifiers
are correct. No repair to the statement is needed. This review neither proves
these propositions nor supplies the missing formal identification of the matrix
with the Fourier-defined source matrix.

## Matrix and indexing

The source symbol is represented exactly at lines 24–26.

The sign and binomial index in lines 28–36 are mathematically correct.
Writing $z=e^{i\theta}$,
$$
(2-z-z^{-1})^m=(-1)^m z^{-m}(1-z)^{2m}.
$$
Its coefficient at exponent $d$ is consequently
$(-1)^d\binom{2m}{m+d}$. Negative exponents give the same coefficient
by binomial symmetry, so using the natural distance of the two matrix
indices is correct. For $d>m$, the lower binomial argument exceeds $2m$
and the coefficient is zero. There is no periodic wraparound or accidental
natural-number subtraction at the edge of the band.

This derivation is an informal check only. Challenge.lean explicitly leaves
the Fourier-integral identification unproved, and its name and comments should
not be read as an existing formal bridge.

The Hermitian proof invokes the symmetry of natural distance, appropriate
for the real scalar field. Mathlib's definition of eigenvalues₀ gives actual
Hermitian eigenvalues with multiplicity, and its adjacent theorem
eigenvalues₀_antitone establishes descending order. The definition at
lines 44–48 uses Fin.rev, whose value is $n-1-j$, to reverse that order.
The cardinality cast does not change the numerical index. Therefore source
index $1$ selects the smallest eigenvalue and source index $n$ the largest.
This does not use an unconstrained eigenvalue placeholder.

The array index is zero-based but lines 50–52 correctly use its value plus
one. Thus the grid is exactly $j\pi/(n+2)$ for source indices $1\le j\le n$.
The natural logarithm and natural ceiling at lines 54–56 give the desired
cutoff. Since $n+2\ge2$, the squared logarithm is positive; natural ceiling
agrees with the usual integer ceiling in this application.

## Coefficients and quantifiers

Coefficients are independent of dimension and index. The infinite natural
indexing is harmless: only entries $0,\ldots,2m$ are used. The functions
are defined on all reals but required to be continuous only on $[0,\pi]$,
matching the canonical problem. Their values outside that interval have no
effect. The leading coefficient agrees with the symbol on the full closed
interval.

The remainder sums precisely over $0,\ldots,p$ and uses denominator
$(n+2)^k$. UniformOrder places positive constant $D$ and threshold $N$
before the universal dimension and eigenvalue quantifiers; neither can vary
with $n$ or $j$. BulkTopOrder restricts the same estimate by comparing
the cutoff with the source index $j+1$.

TargetAt uses one common family for all three assertions. The lower-order
range is $0\le p\le2m-1$, with independent constants allowed for each $p$.
Its negative assertion negates the existence of any global constants for
the order-$2m$ remainder of that same family. FullTarget quantifies over
every natural $m\ge3$, so natural subtraction in $2m-1$ is harmless.
Including dimension zero in UniformOrder is also harmless because Fin 0
has no indices and all assertions are eventual in dimension.

UniversalObstruction separately quantifies over every continuous family;
it does not silently alter the canonical same-family statement. Omitting
a separate leading-symbol condition in this stronger proposition is
appropriate: coefficient uniqueness would force it.

## Precise formalization limits

FullTarget and UniversalObstruction are proposition definitions, not proved
theorems. A successful typecheck proves their well-formedness, not their truth.
The only mathematical theorem in Challenge.lean is the Hermitian property.

The statement is the original continuous-coefficient target. It does not
encode the stronger smoothness assertion for the constructed functions in
the manuscript's Theorem 1. An end-to-end verification of the whole manuscript
would also have to address that additional assertion.

The matrix/Fourier bridge, determinant analysis, endpoint estimates and
indexing, coefficient construction, actual expansion estimates, inverse-kernel
limit, summation limits, even-zeta identity and transcendence input remain
formal proof obligations for an end-to-end MF-21 theorem. The separately
checked helper modules prove narrower conditional results; this statement
review does not eliminate their explicit assumptions.
