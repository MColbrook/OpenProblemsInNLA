# The actual critical-bound fixed-index limit (30)

Locked before ActualFixedIndex.lean, 20 September 2026.

Fix m>=1 and the same actual implicit Y/coefficient family used for all
Taylor and spectral bounds. Assume Y carries the already proved uniform
implicit equation and displacement estimate on its product neighborhood,
and the already proved uniform Taylor estimate at order 2m. The only
new hypothetical premise is the unchanged UniformBound m d (2*m), with
d_k=implicitPhaseCoefficient m Y k.

For every fixed original one-based index j>=1, derive

    (n+2)^(2m) * eigenvalue m n j
      -> pi^(2m) * (j + (m-1)/2)^(2m).

The phase sequence is literally Y(mesh(n,j),1/(n+2)). In particular j
may be below the spectral tail cutoff J. Prove its convergence to zero
using the uniform IFT displacement |Y(x,h)-x|<=C*|h| and mesh=j*pi*h;
do not invoke a tail-only eigenangle estimate. Specialize the uniform
Taylor remainder at the mesh, retaining the full coefficient sum through
2m. Subtract it from the hypothetical critical uniform bound using the
existing checked FixedIndex lemma. The actual endpoint identity
eta(0)=(m-1)*pi/2 gives the displayed literal constant.

The theorem is a fixed-Y implication compatible with all original data
from manuscript_implicit_taylor_with_spectral_error. It does not assume
the desired spectral limit, replace Y, or reselect the coefficient family.
It does not yet assert a reciprocal trace limit, domination, Tannery's
theorem, or the contradiction with the rational trace constant.
