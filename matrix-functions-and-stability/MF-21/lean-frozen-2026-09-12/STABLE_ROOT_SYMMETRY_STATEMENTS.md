# Stable-root symmetry and injectivity: statements before proof

Locked on 20 September 2026 before writing `StableRootSymmetry.lean`.
This continues the root-list prerequisites after the separate initial
`RootDistinctness.lean` submission, without editing that frozen source.

Use only the actual root curve and exponential parameters. First prove:

```lean
theorem stableRootCurve_conj (κ : ℂ) (hκ : 0 < κ.re) (theta : ℝ) :
    (starRingEnd ℂ) (stableRootCurve κ theta) =
      stableRootCurve ((starRingEnd ℂ) κ) theta

theorem stableRootCurve_rootKappa_conj (m ell : ℕ)
    (hell : 1 ≤ ell) (hellm : ell < m) (theta : ℝ) :
    (starRingEnd ℂ) (stableRootCurve (rootKappa m ell) theta) =
      stableRootCurve (rootKappa m (m - ell)) theta
```

Conjugation of the principal square root must be justified by the proved
membership of `1+(κ*sin(theta/2))²` in the slit plane. There is no global
conjugation rule for that square root on its negative-real branch cut.
The actual radicand avoids that cut for every real theta when `Re κ>0`,
so these curve identities legitimately include theta=0 and theta=π.
The parameter conjugacy and the positive-real-part condition for the
published indices must come from the previously proved exact identities.

Then prove pairwise distinctness of the stable roots themselves:

```lean
theorem stableRootCurve_rootKappa_injective
    (m : ℕ) (theta : ℝ) (htheta : 0 < theta) (htheta_pi : theta ≤ Real.pi) :
    Function.Injective (fun ell : {ell : ℕ // 1 ≤ ell ∧ ell < m} =>
      stableRootCurve (rootKappa m ell.val) theta)
```

Derive this from the actual reciprocal equation: equal stable roots have
equal values of `2-r-r⁻¹`, hence equal omega parameters after cancelling
the **proved nonzero** factor `2-2*cos(theta)`. Use the proved injectivity
of the omega parameters. Distinctness is not a premise. The closed upper
endpoint π is allowed; theta=0 is excluded because the stable roots
coalesce there. No positive-m assumption is needed beyond the actual
index subtype, which is empty when m is too small.

This scope does not yet assemble the full 2m-element list. Separating
stable roots from their reciprocals and the two unit roots uses their
modulus gaps; distinguishing the two unit roots requires `0<theta<π`.
Repeated unit roots at the endpoints are not claimed distinct. No phase
sum, determinant estimate, asymptotic expansion, or MF-21 Target follows
without the remaining bridges. No original-problem completion is counted.

Only the new proof module and this lock are edited. The author runs no
compiler; the coordinator performs serial local tests and records any
later Comparator run separately.
