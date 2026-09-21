# One coefficient family: global and bulk expansion bounds

Locked before new expansion-assembly sources, 20 September 2026.

The fixed data are the unchanged actual eigenvalue, symbol, mesh,
expansion, UniformBound and BulkBound definitions. For m>=2 use the
same Y and d_k=implicitPhaseCoefficient m Y k supplied by
manuscript_implicit_taylor_with_spectral_error. No second choice of
coefficient family is allowed when passing from global to bulk bounds.

First prove scalar helpers: for c>0 and natural q there is M>0 bounding
j^q exp(-c*j) for every natural j; the logarithmic-squared cutoff
eventually exceeds any fixed natural J; mesh(n,j) belongs to [0,pi]
for 1<=j<=n; and 1/(n+2) is eventually smaller than any positive radius.
These are conclusions, not additional analytic assumptions.

A fixed-data assembly theorem takes the already proved Taylor estimate
on one positive h radius (all orders p, constants depending on p), the
coefficient vanishing bounds (24) through 2m, and the actual eventual
spectral comparison (25) with constants N,J,C,c independent of n,j.
Its only new spectral premise is the finite-prefix bound

    forall J : Nat, exists C : Real, 0 < C and exists N : Nat,
      forall n>=N, forall j, 1<=j -> j<J -> j<=n ->
        abs(eigenvalue m n j) <= C*(1/(n+2))^(2*m).

This premise is exactly the remaining consequence required from the
circulant/interlacing proof. It is explicit and does not assert any
Taylor expansion or coefficient approximation.

Conclusion: for this same fixed d, UniformBound m d p for every
p<=2m-1. For j below the fixed tail cutoff, (24) bounds each term at
x=j*pi*h by a constant times h^(2m). For the remaining j, polynomial
times exponential decay is uniformly bounded and (25) gives the same
order. Combine with the order-p Taylor estimate and h^(2m)<=h^(p+1)
for 0<h<=1. Constants may depend on m,p and fixed data, never n,j.

A separate fixed-data theorem proves BulkBound m d without any low-index
premise. Use exists_log_sq_bulk_scale_gain with q=2m-1, eventual cutoff
>=J, and the order-2m Taylor estimate. The original cutoff is unchanged:
ceil(log(n+2)^2), including the original one-based condition and j<=n.

Finally provide a wrapper using one existential witness from the actual
implicit/Taylor/spectral theorem. It retains the exact derivative family,
its regularity and d0=symbol; BulkBound is unconditional, while all-index
UniformBound remains an implication from the displayed finite-prefix
premise until that premise is discharged elsewhere. No Target or Part 3
claim follows from these conditional helpers. Smooth-extension
independence is a separate germ theorem, not an assumption here.
