# Diagonal of the actual limiting kernel

Locked before ActualKernelDiagonal.lean, 20 September 2026.

For m>=1 and every x in [0,1], prove for the previously constructed
continuous limiting kernel G that

```
G(m,x,x)=x^(2m-1)*(1-x)^(2m-1)/((2m-1)*((m-1)!)^2).
```

Use the literal upper-half integral, the already checked substitution
in KernelDiagonal, and proved reflection of G. Include x=0,1. Then
prove that the integral of this actual diagonal equals

```
K_m=((2m-1)!)^2/((4m-1)!*(2m-1)*((m-1)!)^2),
```

and that K_m is positive and the cast of a rational. This links the
earlier scalar integral identities to the actual continuous kernel.
Trace convergence is a subsequent obligation, not an assumption here.
