# Concrete finite error expression: statement lock

Locked on 20 September 2026 before writing `MF21Restart/BoundaryErrorBounds.lean`.
The coordinator approved the following actual definitions and exact bounds.
Use the already constructed `normalizedErrorCoefficient` and
`boundaryProductRatio`, with no assumed coefficient or derivative estimate.

The finite index type consists of precisely the nonleading cardinality-m
subsets of the actual ordered characteristic-root indices:

```lean
abbrev BoundaryNonleadingSubset (m : ℕ) (hm : 2 ≤ m) :=
  {s : Finset (Fin (2 * m)) // s.card = m ∧
    s ≠ boundaryLeadingZIndices m (by omega) ∧
    s ≠ boundaryLeadingZInvIndices m (by omega)}

def boundaryErrorTerm (m n : ℕ) (hm : 2 ≤ m)
    (s : BoundaryNonleadingSubset m hm) (theta : ℝ) : ℂ :=
  normalizedErrorCoefficient m (by omega) s.val s.property.1 theta *
    boundaryProductRatio m theta s.val ^ (n + m)

def boundaryErrorExpression (m n : ℕ) (hm : 2 ≤ m) (theta : ℝ) : ℂ :=
  ∑ s : BoundaryNonleadingSubset m hm, boundaryErrorTerm m n hm s theta
```

Prove ordinary local `ContDiff ℝ ⊤` regularity of every term and the
finite expression at each point of `[0,pi]`. This includes local
neighborhood regularity at both endpoints, so the derivatives below
are ordinary real derivatives of complex-valued functions.

The main exact statement is:

```lean
theorem boundaryErrorExpression_exp_bounds (m : ℕ) (hm : 2 ≤ m) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ n : ℕ, ∀ theta : ℝ, 0 ≤ theta → theta ≤ Real.pi →
        ‖boundaryErrorExpression m n hm theta‖ ≤
          C * Real.exp (-c * (n : ℝ) * theta) ∧
        ‖deriv (boundaryErrorExpression m n hm) theta‖ ≤
          C * (n + 1 : ℝ) * Real.exp (-c * (n : ℝ) * theta)
```

Both constants are chosen before n and theta and depend only on m.
The sum is complex-valued; neither its reality nor a determinant identity
is asserted here. Natural n=0 is included, and no large-n hypothesis is
needed for these particular estimates. The interval includes zero and pi.

Derive the ingredients from the actual existing proofs:

1. `normalizedErrorCoefficient_uniform_bound` supplies one positive
   constant for all actual coefficient values and first derivatives.
2. For the actual nonleading ratio functions, derive a common positive
   bound for their first derivatives by local regularity, compactness,
   and a symbolic finite-family bound. This may be exposed as
   `boundaryProductRatio_deriv_uniform_bound`.
3. `boundaryProductRatio_uniform_exp_decay` supplies a single positive c
   bounding every nonleading ratio norm by `exp(-c*theta)`.
4. Use the genuine product and natural-power derivative rules for each
   term. The differentiated power has exponent `n+m-1`, which is at
   least n because m>=2; the value power n+m is also at least n. Thus
   both norm estimates retain `exp(-c*n*theta)` without introducing an
   unproved logarithmic-derivative bound or losing decay at theta=0.
5. The factor n+m in the power derivative is at most m*(n+1). Sum the
   finite term bounds and choose a common positive value/derivative
   constant. Do not enumerate the subsets or use numerical certificates.

Private algebraic norm helpers may take scalar upper bounds as inputs;
the public main theorem must discharge every such bound from the concrete
functions. No determinant estimate, target conclusion, coefficient
regularity, or decay estimate may be added as a public theorem hypothesis.

These are the exponential estimates in manuscript (11) for the chosen
finite expression corresponding to (18), `original-proof/solution.md:122–132`
and `202–215`. Identifying this expression with `D_n/N_n - sin(F_n)`,
proving it real, and proving its value at pi is zero remain separate
leading-coefficient and conjugation obligations. The expression's name
must not be used to claim those identities have already been proved.
The complete MF-21 Target is not established and no original target is
counted. The author runs no compiler; local serialized tests and any
GitHub Comparator evidence remain separate coordinator responsibilities.
