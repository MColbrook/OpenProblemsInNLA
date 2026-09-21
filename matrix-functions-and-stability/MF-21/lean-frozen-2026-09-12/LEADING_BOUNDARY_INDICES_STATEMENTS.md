# Leading Laplace subsets: exact inherited orders and signs

Statement lock before `MF21Restart/LeadingBoundaryIndices.lean`.
Use only the actual sets already defined in `BoundaryProductDecay`:
the exterior indices E={i:m<i.val}, Splus=insert (m-1) E, and
Sminus=insert m E, with `hm : 1 ≤ m` supplying the two Fin indices.
Reuse `card_boundaryLeadingZIndices`; prove the minus cardinality is m.

For j : Fin m, prove the values of the actual `Finset.orderEmbOfFin`
enumerations, with their actual proved cardinalities:

| Inherited sublist | Value of its j-th index |
|---|---|
| Sminus | m+j.val |
| complement of Sminus | j.val |
| Splus | if j.val=0 then m-1 else m+j.val |
| complement of Splus | if j.val=m-1 then m else j.val |

Prove these increasing enumerations using membership and strict monotonicity,
with Mathlib's uniqueness of the increasing enumeration. Do not merely assume
the relevant root sublist is a prepend/append tuple.

Then prove the exact signs in the existing `boundaryLaplaceSign` convention:

```lean
theorem boundaryLaplaceSign_leadingZInv (m : ℕ) (hm : 1 ≤ m) :
    boundaryLaplaceSign m (boundaryLeadingZInvIndices m hm)
      (card_boundaryLeadingZInvIndices m hm) = 1

theorem boundaryLaplaceSign_leadingZ (m : ℕ) (hm : 1 ≤ m) :
    boundaryLaplaceSign m (boundaryLeadingZIndices m hm)
      (card_boundaryLeadingZIndices m hm) = -1
```

For Sminus the split column equivalence is exactly `boundaryRowEquiv m`.
For Splus it is that equivalence followed by swapping the distinct indices
m-1 and m. Prove these equalities from the inherited enumerations, then use
the library sign of a transposition. Thus the unspecified sigma in manuscript
(15) is concretely -1 for the frozen ordering, and the other sign is +1.

There is no root-value, interval, nonvanishing, generic-position, or parity
assumption; these statements are purely about the actual index sets and
existing sign definition. They include m=1 and cover the manuscript's m≥3
domain. Further source will identify the two actual Vandermonde products
and their factors in (15). This file does not claim that factorization,
the normalized determinant identity, or the complete target. No compiler
process, new axioms, or edits to frozen sources are authorized here.
