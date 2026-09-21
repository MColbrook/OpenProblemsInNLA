# Actual normalized root differences: statement lock

Locked on 20 September 2026 before writing `MF21Restart/RootDifferences.lean`.
Use the actual ordered `characteristicRoots` from the unchanged manuscript,
with the orientation `root_j - root_i` used in its Vandermonde factors.
Define the normalized difference by Mathlib's derivative-completed slope:

```lean
def normalizedCharacteristicDifference (m : ℕ) (i j : Fin (2 * m))
    (theta : ℝ) : ℂ :=
  dslope (fun t : ℝ => characteristicRoots m t j - characteristicRoots m t i) 0 theta
```

For m>=2, prove `AnalyticAt ℝ (normalizedCharacteristicDifference m i j) theta`
for every real theta and consequently
`ContDiff ℝ ⊤ (normalizedCharacteristicDifference m i j)`. Here the pinned
Mathlib smoothness order `⊤` is its analytic order; only analyticity in
the **real parameter** is claimed. This follows from the actual root
curves' proved global regularity and the compiled analytic slope theorem.
It does not assume regularity of the normalized function.

The exact endpoint and factorization statements are:

```lean
theorem normalizedCharacteristicDifference_zero
    (m : ℕ) (i j : Fin (2 * m)) :
    normalizedCharacteristicDifference m i j 0 =
      characteristicRootTangents m j - characteristicRootTangents m i

theorem characteristicRoots_sub_eq_mul_normalizedDifference
    (m : ℕ) (i j : Fin (2 * m)) (theta : ℝ) :
    characteristicRoots m theta j - characteristicRoots m theta i =
      (theta : ℂ) * normalizedCharacteristicDifference m i j theta

theorem normalizedCharacteristicDifference_zero_ne_zero
    (m : ℕ) (hm : 2 ≤ m) (i j : Fin (2 * m)) (hij : i ≠ j) :
    normalizedCharacteristicDifference m i j 0 ≠ 0

theorem normalizedCharacteristicDifference_ne_zero
    (m : ℕ) (hm : 2 ≤ m) (i j : Fin (2 * m)) (hij : i ≠ j)
    (theta : ℝ) (htheta : 0 < theta) (htheta_pi : theta < Real.pi) :
    normalizedCharacteristicDifference m i j theta ≠ 0
```

The endpoint value and exact factorization are valid for all m. Their
proof uses the actual endpoint derivative and actual root value one,
respectively. No totalized division by zero is substituted for the slope's
endpoint value. Off zero, the normalized function is exactly
`(theta:ℂ)⁻¹ * (root_j(theta)-root_i(theta))`; this formula may be exposed
as a helper. For nonvanishing, m>=2 and the indicated index inequality
are required; at i=j the normalized function is identically zero.
The positive endpoint π must remain excluded from the general
nonvanishing result because the two oscillatory roots coincide there.

Also define the concrete finite product

```lean
def normalizedCharacteristicDifferenceProduct (m : ℕ)
    (pairs : Finset (Fin (2 * m) × Fin (2 * m))) (theta : ℝ) : ℂ :=
  ∏ p ∈ pairs, normalizedCharacteristicDifference m p.1 p.2 theta
```

Prove its real analyticity at every real point and global `ContDiff ℝ ⊤`
for m>=2. Prove its zero value is
`∏ p ∈ pairs, (characteristicRootTangents m p.2 - characteristicRootTangents m p.1)`.
When every member p of pairs satisfies p.1!=p.2, prove that this product
is nonzero at zero and for every 0<theta<π. The empty product equals one
and is included.

The precise product factorization is valid for all real theta and all m:

```lean
theorem characteristicRoots_differenceProduct_eq_pow_mul
    (m : ℕ) (pairs : Finset (Fin (2 * m) × Fin (2 * m))) (theta : ℝ) :
    (∏ p ∈ pairs, (characteristicRoots m theta p.2 - characteristicRoots m theta p.1)) =
      (theta : ℂ) ^ pairs.card * normalizedCharacteristicDifferenceProduct m pairs theta
```

This supports the removable endpoint factors following manuscript (18),
`original-proof/solution.md:211`. Every factor uses the actual root list;
there is no arbitrary-array regularity or assumed distinctness wrapper.
This module does not yet identify which pairs occur in each determinant
coefficient, count the two Vandermonde exponents, normalize |f|², prove
nonzero denominator values at π, or construct and bound the coefficients
a_S and their derivatives. It does not prove the MF-21 Target or add a
completed original problem. The author does not run a compiler; local
serialized tests and later GitHub Comparator evidence remain separate.
