# Actual ordered root tangents at zero: statement lock

Locked on 20 September 2026 before writing `MF21Restart/RootTangents.lean`.
Use the unchanged `characteristicRoots` definition and its order

`r_1,...,r_(m-1), z, z⁻¹, r_1⁻¹,...,r_(m-1)⁻¹`.

The corresponding actual real-parameter derivatives at zero must be

`-κ_1,...,-κ_(m-1), i, -i, κ_1,...,κ_(m-1)`.

This is the claim at `original-proof/solution.md:211`, following (18).
It is the ingredient needed to establish that every pairwise root
difference has a simple zero. It does not yet cancel products of such
differences or construct the normalized determinant coefficients.

Define the exact list, using the same indices and branches as the roots:

```lean
def characteristicRootTangents (m : ℕ) (i : Fin (2 * m)) : ℂ :=
  if i.val < m - 1 then
    -rootKappa m (i.val + 1)
  else if i.val = m - 1 then
    Complex.I
  else if i.val = m then
    -Complex.I
  else
    rootKappa m (i.val - m)
```

The primary exact statements are:

```lean
theorem characteristicRoots_zero (m : ℕ) (i : Fin (2 * m)) :
    characteristicRoots m 0 i = 1

theorem characteristicRoots_hasDerivAt_zero (m : ℕ) (i : Fin (2 * m)) :
    HasDerivAt (fun theta : ℝ => characteristicRoots m theta i)
      (characteristicRootTangents m i) 0

theorem characteristicRootTangents_injective (m : ℕ) (hm : 2 ≤ m) :
    Function.Injective (characteristicRootTangents m)

theorem characteristicRoots_sub_hasDerivAt_zero
    (m : ℕ) (a b : Fin (2 * m)) :
    HasDerivAt
      (fun theta : ℝ => characteristicRoots m theta a - characteristicRoots m theta b)
      (characteristicRootTangents m a - characteristicRootTangents m b) 0

theorem characteristicRootTangents_sub_ne_zero
    (m : ℕ) (hm : 2 ≤ m) (a b : Fin (2 * m)) (hab : a ≠ b) :
    characteristicRootTangents m a - characteristicRootTangents m b ≠ 0
```

Endpoint value and derivative statements are valid without restricting
m: the list is empty at m=0, while at m=1 it contains exactly z and z⁻¹.
The natural domain requested for pairwise distinctness is m>=2. No
distinctness, derivative, branch, or nonzero-difference condition is
introduced as an assumption.

Derive the stable derivatives from the compiled
`stableRootCurve_hasDerivAt_zero`; differentiating reciprocals at the
proved value one gives the exterior derivatives with the opposite sign.
Differentiate the actual exponential for the unit roots. All derivatives
are of maps from ℝ to ℂ with respect to the real parameter theta.

For tangent injectivity, the stable tangents have strictly negative real
part, the exterior tangents have strictly positive real part, and the
two unit tangents have real part zero and distinct imaginary parts.
Within each stable/exterior group, square equality of κ values and use
the proved identity `rootKappa_sq` together with `rootOmega_injective` on
`Fin m`. This must prove distinctness of the concrete parameters; it may
not assume a distinct root or tangent list. Optional helper statements
may expose the κ injectivity and the two real-part regions.

These results supply one analytic ingredient for the original manuscript.
They do not establish determinant normalization, its vanishing order,
uniform coefficient bounds, the spectral asymptotics, or the complete
MF-21 Target. They add no completed original target. The author runs no
compiler; source-matched serialized local testing and eventual GitHub
Comparator testing remain separate coordinator responsibilities.
