# Referee B: actual Fourier binomial stencil

Verdict: **APPROVE**, scoped to
`fourierStencilPolynomial_eq` and `fourierCoeff_shifted_binomial` in
`MF21Restart/FourierBinomialStencil.lean`. The reviewer did not author or
edit this module and ran no compiler. This review concerns an exact
coefficient bridge, not a matrix inverse or kernel-convergence theorem.

## Source and local evidence

| Item | SHA-256 |
| --- | --- |
| `MF21Restart/FourierBinomialStencil.lean` | `ce61bed56422d9c0b26ed80c5aa308eaf38b73bcf30d987d882f84be8031c0d1` |
| `FOURIER_BINOMIAL_STENCIL_STATEMENTS.md` | `957d8850cfa6f262e8aef6439e2e100b15a5f70c05c788633128c0bb730e9e92` |
| `evidence/logs/fourier-binomial-stencil-02.json` | `f64231beb25ed2e0793ebf4b9890ec6aa80d9e46650bb406f8442caa59ae3511` |
| `evidence/logs/fourier-binomial-stencil-02.log` | `4b96bbcb5e63bf222bfd17aff69c2ab195c4846b33e8022398003b69f3aa1252` |
| `.lake/build/lib/lean/MF21Restart/FourierBinomialStencil.olean` | `f0d101b11d8235d0fe5b3283e307eaa5da635e23308409f11263a16851a4120a` |
| Imported `MF21Restart/FourierRecurrence.lean` | `99c431d06aea02d723c4e95e4b8aabcff51af0fc5b0cc0bca0b95d1bddaab9c8` |
| Imported `MF21Restart/FourierLaurent.lean` | `ffa0cb9a4f88ba83f76d5101875fc9e8065bbc3c7e582e0808be6bc939c69dad` |

The reviewer recomputed the source, log, and output hashes and matched
them to the retained JSON. It records unchanged source, exit code 0,
`LEAN_NUM_THREADS=1`, and

```
lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/FourierBinomialStencil.olean MF21Restart/FourierBinomialStencil.lean
```

The observed log prints the two named declarations with only `propext`,
`Classical.choice`, and `Quot.sound`. This is source-matched local
development evidence; no GitHub Comparator check is claimed.
The unchanged manuscript hash is
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`;
the pinned referee rubric hash is
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Statement and proof review

The polynomial at lines 24–27 is formed from the existing integral
`fourierCoeff`; that definition retains its factor `1/(2*pi)` and the
unchanged symbol. The new module neither redefines the coefficient nor
substitutes a binomial matrix for `toeplitz`. Its integer frequency is
`(t : Z)-(m : Z)`, while polynomial degree `t` remains a natural number.

`fourierStencilPolynomial_eq` (line 31) applies the existing proved
Laurent identity only to nonzero complex arguments. The exact algebra
is `z*(2-z-z^(-1))=-(1-z)^2`, giving the global sign `(-1)^m` and
degree `2*m`. Equality on the infinite complement of `{0}` identifies
the two actual polynomials, so evaluation at the excluded Laurent
point zero is never used. The imported shifted Laurent statement was
also inspected: its finite reindexing keeps precisely frequencies
`[-m,m]`, and its nonzero hypothesis justifies the integer-power law.

The coefficient-extraction helper at line 55 uses the hypothesis
`t<=2*m` to select the unique index in `Fin(2*m+1)`. The helper at
line 74 rewrites the even power of `1-X` as the even power of `X-1`
and applies the library binomial formula. Its parity conversion
`(2*m-t) mod 2 = t mod 2` is used with the necessary `t<=2*m` premise;
it does not silently replace truncated subtraction outside that range.

The public real coefficient formula at line 94 includes the factor
`(-1)^(m+t)` and is obtained by complex coefficient equality followed
by injectivity of the real embedding. Algebraic edge checks agree with
the normalization: `m=0,t=0` gives one; `m=1` gives `[-1,2,-1]` on
frequencies `[-1,0,1]`; the central coefficient is positive; and both
support endpoints have sign `(-1)^m`. These are semantic checks rather
than unreported executions. Coefficients outside the support remain
covered by the existing `fourierCoeff_support` theorem, as the lock
explicitly requires.

No material issue was found. There is no new numerical certificate,
assumed generating identity, custom axiom, or analytic continuation
assumption. The polynomial-equality method uses standard exact Mathlib
APIs. The result is a valid bounded ingredient for proving the cited
inverse-kernel input in manuscript Section 5, lines 312–320; it does
not itself establish that input, weighted factorization, inverse entries,
or any original-target completion.
