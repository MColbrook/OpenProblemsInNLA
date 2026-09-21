# Statement lock: exact increasing circulant spectrum

Locked before source on 20 September 2026. This is the next bounded stage
of `CIRCULANT_INTERLACING_STATEMENTS.md`; the actual circulant and its full
complex characteristic polynomial have already been locally tested.

Define the one-based value formula, totalized for all natural indices,

```
circulantOrderedValue m N j = symbol m (2*pi*((j/2 : Nat) : Real)/(N : Real)).
```

The assertions only use positions `j=1,...,N` and `m<N`; monotonicity and
the sorted-list assertion additionally use `1<=m`.

`CirculantOrder.lean` will prove:

1. The real characteristic polynomial of the actual `fourierCirculant m N`
   is the product of `X-C(symbol m (2*pi*ell/N))` over all `ell : Fin N`.
   This follows by injectivity of real-to-complex polynomial mapping from
   the already proved complete complex characteristic polynomial.
2. Its real characteristic polynomial is also the product of
   `X-C(circulantOrderedValue m N (i.val+1))` over all `i : Fin N`.
   A genuine permutation of the frequency indices proves this: the
   permutation is `0,1,N-1,2,N-2,...`. Injectivity and finite cardinality
   establish bijectivity. The reflected frequency values agree by
   `cos(2*pi-theta)=cos(theta)`. This preserves all multiplicities.
3. The tuple `i -> circulantOrderedValue m N (i.val+1)` is monotone.
   The frequency angles lie in `[0,pi]`; the previously proved strict
   monotonicity of the actual symbol implies this non-strict tuple order.
4. The increasing multiset sort of the actual Hermitian eigenvalues of
   `fourierCirculant m N` equals exactly the `List.ofFn` of this tuple.
   It follows from equality of the characteristic-root multisets and the
   tuple's proved order, not from equality of sets of spectral values.

The first value is the frequency zero. Every positive frequency is paired
with its negative except the final frequency pi for even N. For odd N,
the largest frequency below pi is still paired. The permutation proof
must cover both parities and all endpoint indices without removing a
duplicate root. These results will later feed a proved finite-dimensional
interlacing argument for the original Toeplitz principal block.

This module does not itself prove interlacing, manuscript (21) or (22),
an inverse-trace estimate, or the full MF-21 target. Only the coordinator
runs the serialized local tests; Comparator remains separate.
