# Actual inverse on the upper-half grid

Locked before InverseKernelGridTop.lean, 20 September 2026.

Definitions: for i:Fin n, X(n,i)=(i+1)/n, so these are the manuscript's
one-based grid points, including X(n,n-1)=1. Define

```
Ktop(m,x,y) = integral_{max(x,y)}^1 F(m,0,x,y,t).
```

Since F(m,0,x,y,t) is the exact expression already proved in
finiteKernelIntegrand_zero_step, Ktop is literally (27), with its constant
prefactor inside the integral. No operator identity is assumed here.

First prove the exact reindexing of the actual finite inverse:

```
n^(-(2m-1)) * (A_n^-1)[i,j]
 = (1/n) * sum_{k=max(i,j)}^{n-1} F(m,1/n,X(n,i),X(n,j),(k+1)/n).
```

This retains the lower index max(i,j), NOT max(i,j)+1, because Fin indices
are zero based. Its integration lower endpoint becomes max(X(n,i),X(n,j))
after a displacement exactly 1/n, already covered by the shifted-sum bound.

Then for each fixed m>=1 and epsilon>0 prove that for some N>=4, all n>=N
and all i,j:Fin n with X(n,i)+X(n,j)>=1 satisfy

```
abs(n^(-(2m-1)) * (A_n^-1)[i,j] - Ktop(m,X(n,i),X(n,j))) <= epsilon.
```

There is no assumption of a spectral or kernel limit. Upper-half geometry
gives max(i,j)/n >= 1/2-1/n >= 1/4, so all compact integrand bounds apply.
Reflection, continuity of the assembled kernel, and passage from grid to
every point of the square remain separate obligations.
