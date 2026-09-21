# Actual circulant embedding and spectral interlacing

Locked 20 September 2026 before the corresponding proof sources.
This fixes the literal obligations in manuscript (21)–(22), using
the unchanged actual `toeplitz`, `orderedEigenvalue`, and one-based
`eigenvalue` definitions. It is a development lock, not a claim that
the several obligations below have already been proved or tested.

Write a_k=`fourierCoeff m k`. For N>m define the length-N first column

```
periodicFourierColumn m N k = a_(k.val) + a_(k.val-N),  k : Fin N,
fourierCirculant m N = Matrix.circulant (periodicFourierColumn m N).
```

Here `Matrix.circulant v i j=v(i-j)`, with subtraction in Fin N. This
column includes both Fourier terms at a residue when the support
overlaps modulo N; no term is silently dropped. The constructor is
total for all m,N, but spectrum assertions use N>m.

The first bounded module `CirculantEmbedding.lean` must prove:

1. For m<N and i,j:Fin N, with integer d=i.val-j.val,
   `fourierCirculant m N i j = a_d+a_(d+N)+a_(d-N)`.
2. This actual circulant is real Hermitian for m<N.
3. With N=n+2*m, m>=1, and the literal leading-index embedding
   `e i = Fin.castLE (Nat.le_add_right n (2*m)) i`,
   `(fourierCirculant m N).submatrix e e = toeplitz m n`.

The third statement includes all n, including the empty n=0 block.
For actual entry pairs, |d|<=n-1, so both shifted frequencies have
absolute value at least 2m+1>m. Their actual integral coefficients
vanish by the already proved finite Fourier support theorem. This
is the no-wrap argument; it is not a claim that an arbitrary
circulant has the required leading block.

The subsequent spectrum obligation is to prove, rather than assume,
that this actual circulant's characteristic-root multiset consists
of `symbol m (2*pi*ell/N)` for ell=0,...,N-1, counted with multiplicity.
It can be stated after complexification as the exact characteristic
polynomial product, then transferred to the real Hermitian spectrum.
The existing actual Laurent identity supplies each Fourier-mode
eigenvalue. Fourier invertibility or the distinct-root Vandermonde
basis must supply all N eigenvectors; membership alone is insufficient.

Put

```
mu m N j = symbol m (2*pi*((j/2 : Nat) : Real)/(N : Real)).
```

The sorted-spectrum obligation identifies the increasing list of
actual circulant eigenvalues with `mu m N 1,...,mu m N N`.
This is one-based: j=1 gives zero; the positive frequencies occur in
pairs; for even N the last term is the single frequency pi, and for
odd N the largest frequency occurs twice below pi. The parity and
last-index cases are part of the proof. The displayed samples are
not used as an assumed sorted eigenvalue list.

The final actual interlacing statement, for m>=1, 1<=j<=n, N=n+2m, is

```
mu m N j <= eigenvalue m n j <= mu m N (j+2*m).
```

It must follow from the proved leading principal block and an actual
Hermitian interlacing argument, with no interlacing, spectral order,
eigenvalue formula or rank bound supplied as a public premise.
The library search found no pre-existing Cauchy interlacing or
Courant–Fischer theorem in the pinned Mathlib; if a general finite
dimension argument is introduced, it will be proved from eigenbases,
quadratic forms and finite-dimensional linear algebra.

The numerical consequences are the following exact inequalities,
again for the original one-based eigenvalue, m>=1 and 1<=j<=n:

```
eigenvalue m n j <=
  (pi * ((j+2*m : Nat) : Real) / ((n+2*m : Nat) : Real))^(2*m),

(4 * ((j/2 : Nat) : Real) / ((n+2*m : Nat) : Real))^(2*m)
  <= eigenvalue m n j.
```

For j>=2, also prove the displayed manuscript (22) comparison

```
(4*(j : Real)/(3*((n+2*m : Nat) : Real)))^(2*m)
  <= eigenvalue m n j.
```

The upper inequality immediately supplies the fixed-low-index bound
of order n^(-2m), since n>0 and n<=n+2m. The lower inequality at j=1
is only zero, as the manuscript requires; no positive lower bound
of that form is falsely asserted there. Jordan's sine inequality and
sin(t)<=t are used on the proved frequency interval [0,pi]. No
floating-point spectral sampling or matrix-size computation is used.

Each source module will state its completed subset of these obligations
and print axioms for its public results. Neither this lock nor a partial
component asserts a completed MF-21 Target or increments a target count.
No source agent runs a compiler; the coordinator owns serialized local
tests. Comparator remains a separate unrun final check.
