# Phase extension: locked statements before proof

For `κ : ℂ` with `0 < κ.re`, use the actual quadratic root already defined
as `stableRootCurve κ θ`. Put `s = sin(θ/2)`, `b = sqrt(1+(κ*s)^2)` and

```
Pκ(θ) = exp(-iθ) * (κ*b + i*cos(θ/2) - (1+κ^2)*s).
```

The exact identity to establish is
`1 - stableRootCurve κ θ * exp(-iθ) = (2*sin(θ/2))*Pκ(θ)`.
This is the manuscript's simple-zero factorization with a smooth positive
factor `2*sin(θ/2)` on `0 < θ ≤ π`; its first derivative at zero is one.
The normalized factor is smooth on the real line and has value `κ+i` at
zero. It has strictly positive real part on `[0,π]`.

Define the individual extended phase to be `arg(Pκ(θ))`, not the argument
of a product. Prove it is smooth at every point of `[0,π]` and equals
the original `arg(1-rκ(θ)*exp(-iθ))` for positive θ in that interval.
Use the imaginary part of the complex logarithm only to prove local
smoothness on the right half-plane, preserving the actual principal arg.

No root-of-unity index identities, summed endpoint phase, determinant
normalization estimate, or spectral conclusion is assumed or claimed by
this module. Those are separate remaining obligations.
