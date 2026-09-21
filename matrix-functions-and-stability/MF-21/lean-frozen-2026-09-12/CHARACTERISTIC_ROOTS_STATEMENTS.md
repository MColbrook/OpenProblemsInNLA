# Exact ordered characteristic roots: statements before proof

Locked on 20 September 2026 before writing `CharacteristicRoots.lean`.
Construct the literal ordered list in the frozen manuscript immediately
before equation (13), `original-proof/solution.md:142–147`:

`r_1,...,r_(m-1), z, z⁻¹, q_1,...,q_(m-1)`

where `z=exp(i*theta)`, `r_ell=stableRootCurve (rootKappa m ell) theta`,
and `q_ell=r_ell⁻¹`. Definitions are total in natural m, but the actual
ordered-list claims use `m>=2`:

```lean
def oscillatoryRoot (theta : ℝ) : ℂ :=
  Complex.exp ((theta : ℂ) * Complex.I)

def characteristicRoots (m : ℕ) (theta : ℝ) (i : Fin (2 * m)) : ℂ :=
  if i.val < m - 1 then
    stableRootCurve (rootKappa m (i.val + 1)) theta
  else if i.val = m - 1 then
    oscillatoryRoot theta
  else if i.val = m then
    (oscillatoryRoot theta)⁻¹
  else
    (stableRootCurve (rootKappa m (i.val - m)) theta)⁻¹
```

Prove these public results:

```lean
theorem characteristicRoots_ne_zero
    (m : ℕ) (theta : ℝ) (i : Fin (2 * m)) :
    characteristicRoots m theta i ≠ 0

theorem characteristicRoots_injective
    (m : ℕ) (hm : 2 ≤ m) (theta : ℝ)
    (htheta : 0 < theta) (htheta_pi : theta < Real.pi) :
    Function.Injective (characteristicRoots m theta)

theorem characteristicRoots_equation
    (m : ℕ) (hm : 2 ≤ m) (theta : ℝ) (i : Fin (2 * m)) :
    (2 - characteristicRoots m theta i - (characteristicRoots m theta i)⁻¹) ^ m =
      (symbol m theta : ℂ)
```

Every definition must use the unchanged actual Fourier symbol and root
curves, not an arbitrary root list with the desired properties as inputs.
The stable indices are exactly i+1 for `0<=i<m-1`, and the exterior
indices are exactly i-m for `m<i<2*m`; both run in increasing order from
1 through m-1. All natural subtraction and range facts are justified.

Nonvanishing follows from the proved concrete curve nonvanishing and
the actual exponential. Stable-root pairwise distinctness comes from
`StableRootSymmetry`; the reciprocals retain that distinctness. The
proved strict norm bounds separate the stable, unit, and exterior groups.
The two unit roots differ because `sin(theta)>0` for `0<theta<pi`.
Neither endpoint may be included in the full-list injectivity theorem:
the unit roots coincide there, and the stable roots also coalesce at zero.

Each stable-root equation uses the proved omega power identity; taking
the m-th power eliminates omega. Inversion preserves `2-w-w⁻¹`, and
the unit roots yield `2-2*cos(theta)` directly. Identify its m-th power
with the unchanged `symbol m theta` using the proved
`symbol_eq_cosine_power`. This algebraic equation is valid for every real
theta; it does not require interval or distinctness assumptions.

Auxiliary results may expose the unit-root norm/inverse identity and the
two norm regions of the list. They must be proved from these concrete
definitions. This module supplies the root-list hypotheses required by
the existing boundary determinant/eigenvalue bridge; it does not prove
determinant normalization or error estimates, phase indexing, asymptotic
expansions, or the complete MF-21 Target. No original-problem completion
is counted. The author edits only this new lock and source, runs no
compiler, and leaves serialized local testing to the coordinator.
