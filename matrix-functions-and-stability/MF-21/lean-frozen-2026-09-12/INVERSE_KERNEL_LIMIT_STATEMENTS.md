# The literal step-kernel uniform limit (26)

Locked before InverseKernelLimit.lean, 20 September 2026.

For n>0 and x in [0,1], define the Fin n index as
min(ceil(n*x)-1,n-1), using natural truncated subtraction. This is exactly
the manuscript's ceil(n*x) interpreted in one-based indices, clamped at
the endpoints. In particular x=0 uses the first index and x=1 the last.
Prove that its one-based grid point X satisfies x<=X<=x+1/n, including
both endpoints. No claim of exact reflection without the one-cell shift
is made.

Define the actual step kernel by n^{-(2m-1)} times the inverse entry at
these two indices. For each fixed m>=1 and epsilon>0, prove that there is
N>=4 such that for every n>=N and every x,y in [0,1],

```
abs(stepKernel(m,n,x,y)-G(m,x,y)) <= epsilon.
```

This is a pointwise-uniform version of the essential-uniform limit (26),
with a concrete continuous G having the literal upper formula (27) and
the exact reflection already proved. Use the actual all-grid limit and
uniform continuity of G. In particular, the diagonal is covered directly.
This theorem does not yet assert trace convergence or a differential
operator interpretation of G.
