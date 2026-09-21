# Exact spectrum of the actual Fourier circulant

Locked 20 September 2026 before `CirculantSpectrum.lean`, as the next
stage of `CIRCULANT_INTERLACING_STATEMENTS.md`.

For natural m,N with m<N, use the already defined actual
`periodicFourierColumn` and `fourierCirculant`. Prove:

```
periodicFourierColumn_laurent_sum (m N : Nat) (hmN : m<N)
    (z : Complex) (hz : z!=0) (hzN : z^N=1) :
  sum k:Fin N, (periodicFourierColumn m N k : Complex)*z^k.val
    = (2-z-z⁻¹)^m
```

The proof folds the actual supported integer Laurent coefficients into
the two residues k and k-N. The finite interval [-N,N) contains the
support [-m,m], and z^N=1 identifies their powers. No unsupplied
summability or Fourier-transform formula is a premise.

For each ell:Fin N let z=`rootOmega N ell.val`, the existing literal
complex exponential exp(2*pi*i*ell/N). Prove the matrix-vector identity

```
((fourierCirculant m N).map Complex.ofReal).mulVec
    (fun i:Fin N => z^i.val)
  = fun i:Fin N =>
      (symbol m (2*pi*(ell.val:Real)/(N:Real)) : Complex)*z^i.val.
```

Finally prove the exact characteristic polynomial, including all
multiplicities:

```
((fourierCirculant m N).map Complex.ofReal).charpoly =
  product ell:Fin N,
    (Polynomial.X - Polynomial.C
      (symbol m (2*pi*(ell.val:Real)/(N:Real)) : Complex)).
```

The proof must show that all N geometric vectors form a basis. The
existing proved injectivity of `rootOmega N` on Fin N gives nonzero
Vandermonde determinant. The explicit intertwining identity with the
diagonal matrix then gives the characteristic polynomial by matrix
similarity. Merely proving each sampled value is an eigenvalue does
not suffice when sampled values repeat.

The angle and sign are checked through the literal symbol identity
`(2-z-z⁻¹)^m=(symbol m theta : Complex)` at z=exp(i*theta).
The scope includes m=0,N>0, when every spectral value is one. N=0
is excluded by m<N. No eigenvalue order, circulant spectrum, basis
invertibility, or interlacing conclusion is assumed.

Increasing spectral enumeration, the real one-based accessor bridge,
interlacing, and estimates (21)–(22) remain subsequent obligations.
This module does not complete MF-21. Source authors run no compiler;
the coordinator retains actual serialized local evidence. Comparator
remains a separate unrun check.
