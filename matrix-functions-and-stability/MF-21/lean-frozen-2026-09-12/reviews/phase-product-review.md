# Independent review: actual phase product

Verdict: **APPROVE**, for the eight printed results in the agent-authored
`MF21Restart/PhaseProduct.lean`. This reviewer did not author, edit, or
compile that module. Upstream `PhaseZero.lean` includes work by this
reviewer and is an imported proved interface here, not newly independently
reviewed by its author. This report is restricted to the product,
factorization, polar and conjugate-quotient logic.

The unchanged manuscript SHA-256 is
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`;
the pinned referee rubric SHA-256 is
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

| Reviewed item | SHA-256 |
| --- | --- |
| `MF21Restart/PhaseProduct.lean` | `1a4e719778fff8ed729c9bb6cc5f7615cf5d2aa0696b8df302c107afd64afeb1` |
| `PHASE_PRODUCT_STATEMENTS.md` | `badb60d2390d107284df1ceb7f3b8469cf5811abb30d460875b9abbce0f3a17c` |
| Imported `MF21Restart/PhaseZero.lean` | `ac803ba9621d41d11d7ccff77c53299fdf6f13f9caf98e99b6692d4a3cb78885` |
| Imported `MF21Restart/PhaseFactor.lean` | `4b681c97f6c26935ab1a495703f9d648c7fb36c77746d47f9637e6fe741be238` |

The definitions at lines 18–24 are the literal product
`f=prod (1-r_ell*z^(-1))` from manuscript lines 171–174 and its normalized
factor product. `ell : Fin(m-1)` gives exactly the root indices
`ell.val+1=1,...,m-1`. The m=1 products are empty and equal one; the
unrestricted total definitions at m=0 likewise introduce no invalid
root-parameter premise because the index type is empty.

`normalizedPhaseProduct_contDiff`, its zero value and its nonvanishing
(lines 26–49) are derived from the actual factors' regularity, values,
and positive real parts. Nonvanishing on `[0,pi]` is not assumed.

`normalizedPhaseProduct_polar` (lines 52–76) multiplies the individual
identities `P_ell=norm(P_ell)*exp(i*arg(P_ell))`. It then uses the product
of norms and the exponential of the **sum** of individual arguments.
The equality at lines 61–64 identifies this sum with the actual
`manuscriptPsi`, without equating it to the principal argument of the
product. A sum exceeding pi causes no problem. The all-real-theta
statement remains valid even if a factor vanishes outside the specified
interval, because the individual polar identity is still valid with
zero norm. There is no branch trap or hidden nonzero assumption here.

`manuscriptPhaseProduct_factorization` (lines 78–100) retains exactly
`m-1` factors of `2*sin(theta/2)` and the inverse unit exponential's
negative sign. It is a global algebraic identity. The actual product's
nonzero and polar identities (lines 108–141) are correctly restricted to
`0<theta<=pi`, where that real scalar is positive. They do not drop its
possible sign outside the interval or assert that f is nonzero at zero
for m>=2.

`manuscriptPhaseProduct_div_conj` (lines 144–179) cancels the common norm
only after proving it nonzero. Conjugating the denominator negates its
phase, so division gives `exp(i*psi-(-i*psi))=exp(+2*i*psi)`. The plus
sign is correct for manuscript (15)–(16). The upper endpoint pi is valid;
the lower endpoint zero is correctly excluded from this quotient.
No numerical certification or new axiom is involved. The unused `hm`
warning in the polar statement is optional generality polish, not a
fidelity or proof issue.

The reviewer read `evidence/logs/phase-product-01.json`, SHA-256
`a1103066e919ec9dcbc32d8f9bf4f9140582337758968d0ce6e37d8b3a95b815`,
which records the actual command
`lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/PhaseProduct.olean MF21Restart/PhaseProduct.lean`,
exit code zero and unchanged source. Source, log and output hashes were
independently recomputed and matched. The log hash is
`43337936c60a56e35561bc8414e4f93fa18ec41692f01c477e1603eb7a16d9a7`;
all eight reports contain only `propext`, `Classical.choice`, `Quot.sound`.
The output hash is
`16ee566ef09f741fb011cd81593dc47422871a154138dd1ac2cb1de7185bac24`.

This is a scoped local source/evidence review, not a Comparator run or
a complete MF-21 verification. It does not prove the leading coefficient
identities, eigenvalue indexing, or the final target. No material issue
was found.
