# Statement lock: finite-dimensional diagonal-form interlacing

Locked before source on 20 September 2026. This is a proved linear-algebra
component for the actual principal-block interlacing obligation. It will
not be substituted for the actual matrix result: a later module must
construct its linear map from actual orthonormal eigenbases and the proved
Toeplitz/circulant principal embedding, and discharge both identities below.

For `n<=N`, monotone real arrays `a : Fin n -> Real` and
`b : Fin N -> Real`, and a real linear map
`L : (Fin n -> Real) -> (Fin N -> Real)`, suppose exactly

```
sum_j (L x j)^2 = sum_i (x i)^2,
sum_j b j*(L x j)^2 = sum_i a i*(x i)^2
```

for every x. Prove for every zero-based `i : Fin n`:

```
b (castLE i) <= a i,
a i <= b (i.val + (N-n)).
```

The last index is supplied with its genuine `Fin N` bound. Both arrays
retain repeated entries. There is no definiteness or strict-order premise.
The empty case n=0 is allowed and has no in-range assertions.

The lower bound follows by mapping the `(i.val+1)`-dimensional space of
first coordinates into the `i.val` lowest ambient coordinates. Strict
dimension inequality produces a nonzero kernel vector. Its quadratic
form in the smaller array is at most `a i` times its squared norm; in the
ambient array it is at least `b i` times the same squared norm. Cancellation
of this positive norm proves the inequality. Reversing both coordinate
orders and negating both arrays reduces the upper bound to this lower
bound. This is the finite-dimensional argument, not an assumed min-max or
interlacing theorem.

A concrete initial-coordinate extension by zero is defined and proved
linear; it is reused in the kernel argument and may be reused for actual
matrix compression. Only the coordinator runs serial local Lean tests.
This generic component is not an actual Toeplitz eigenvalue estimate or
a completed original target.
