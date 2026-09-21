# Root-list prerequisites: statements before proof

Initial scope locked on 20 September 2026, before writing
`RootDistinctness.lean`. Use the actual exponential definitions in
`RootParameters.lean`, which match manuscript equations (2) and (8).
Prove these three prerequisites without any assumed root-of-unity,
distinctness, periodicity, or conjugacy certificate:

```lean
theorem rootOmega_pow (m ell : ℕ) (hm : 1 ≤ m) :
    rootOmega m ell ^ m = 1

theorem rootOmega_injective (m : ℕ) :
    Function.Injective (fun ell : Fin m => rootOmega m ell.val)

theorem rootKappa_conj (m ell : ℕ)
    (hell : 1 ≤ ell) (hellm : ell < m) :
    (starRingEnd ℂ) (rootKappa m ell) = rootKappa m (m - ell)
```

The m-th power statement requires `m>=1`, so division by m in its proof
is justified. The injectivity theorem uses the full half-open natural
index range `0<=ell<m`; `Fin 0` is empty, so no extra positive-m premise
is needed. The injectivity proof must use actual exponential angle
injectivity on an interval of length 2π, with the correct half-open
endpoint convention, and exact real division by m.

The κ conjugacy theorem applies to the original stable indices
`1<=ell<m`. Natural subtraction `m-ell` is therefore controlled before
casting, and maps that range to itself. Prove the real angle at m-ell is
the negative of the angle at ell, then use conjugation of the actual
complex exponential.

This first module scope does not yet assert stable-root injectivity,
stable-root conjugacy, or distinctness of the entire 2m-element
characteristic root list. Those require separate derived lemmas using
the actual reciprocal equations and branch conditions. In particular,
principal square root must not be assumed to commute with conjugation
on its negative-real branch cut. Any extension of this lock must precede
the corresponding proof additions.

No endpoint phase sum, asymptotic estimate, complete Lemma 2, or MF-21
Target is claimed. No original-problem completion is counted. Only the
new source and this lock are edited; the author runs no Lean compiler.
The coordinator supplies serialized local tests and records any later
GitHub Comparator run separately.
