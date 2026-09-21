# A shifted-endpoint uniform kernel sum

Locked before KernelShiftedSum.lean, 20 September 2026.

For each fixed natural m, use the exact finiteKernelIntegrand F already
derived from the actual inverse, not a newly chosen approximant. Expose its
continuity in t on [1/4,1] when h,x,y belong to [0,1].

Prove: for every epsilon>0 there is N>=4 such that for all n>=N,
x,y in [0,1], integers 0<=a<=n satisfying a/n>=1/4, and real b with
a/n<=b<=1 and b-a/n<=1/n,

```
abs((1/n) * sum_{k=a}^{n-1} F(m,1/n,x,y,(k+1)/n)
    - integral_b^1 F(m,0,x,y,t)) <= epsilon.
```

The quantification is uniform in x,y,a,b. The case a=n,b=1 is included.
No limit or integrability assertion is assumed. The proof combines the
already proved uniform right-sum estimate, uniform h-to-zero continuity,
and a compact bound times the endpoint displacement. All interval lengths
are bounded by one. Taking b=max(x,y) will be justified separately from
the actual one-based grid and guarded inverse sum.

This lemma alone is not the uniform inverse-kernel theorem (26).
