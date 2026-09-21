# Uniform convergence on the whole actual grid

Locked before InverseKernelGrid.lean, 20 September 2026.

For every fixed m>=1 and epsilon>0 prove that there is N>=4 such that,
for every n>=N and every i,j:Fin n,

```
abs((1/n)^(2m-1) * (A_n^-1)[i,j] - G(m,X(n,i),X(n,j))) <= epsilon.
```

Here A is the actual integral-defined Toeplitz matrix, X(n,i)=(i+1)/n,
and G is the continuous reflected literal kernel constructed previously.
The theorem has no assumption of convergence or smallness of an error.

The upper-half result is already proved. In the other half use the exact
finite inverse reversal and prove explicitly the one-based identity

```
X(n,i.rev) = 1-X(n,i)+1/n.
```

In particular the reflected discrete points are displaced from the reflected
continuous points by 1/n in BOTH coordinates. They lie in the upper half.
Compact uniform continuity controls that displacement, and the exact
reflection identity of G completes the estimate. Do not silently drop
the one-cell shift. Boundary points and the last index are included.
