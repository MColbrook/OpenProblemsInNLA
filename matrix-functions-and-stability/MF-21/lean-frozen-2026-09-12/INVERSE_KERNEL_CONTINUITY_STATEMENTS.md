# The continuous kernel with the manuscript's reflection

Locked before InverseKernelContinuity.lean, 20 September 2026.

Construct one function G(m,x,y) on the real square. On x+y>=1 it equals
inverseKernelTop, the literal integral in (27). On the other half it equals
the same formula at (1-x,1-y). Prove continuity, symmetry in x,y, and
G(m,1-x,1-y)=G(m,x,y). In particular it is uniformly continuous on [0,1]^2.

For a convenient global continuous extension of the upper formula, clamp
only the integration variable below 1/4 inside F(m,0,x,y,t). The denominator
then never vanishes. This does not change any integral on x+y>=1: both
integration endpoints and every point between them are >=1/2. The limiting
kernel itself is defined by the extension on the two reflected halves, and
its equality with the literal unclamped integral is proved, not assumed.

The two expressions agree on x+y=1 because reflection there swaps x and y
and the exact integrand is symmetric. This supplies the gluing proof,
including the corner points. There is no assumed Green-operator or kernel
convergence theorem. These statements only supply the continuous concrete
kernel needed for the grid-to-square convergence proof.
