# Actual simple residual roots: statement lock

This lock precedes `MF21Restart/ActualSimpleRoots.lean`. It records only
the concrete simple-root bridge used in manuscript Lemma 4. The existing
manuscript, matrix, eigenvalues, characteristic roots, normalizer, phase,
and error expression are unchanged.

For natural `m,n` and `hm : 2 ≤ m`, define the real function

```
manuscriptResidual m n hm θ :=
  Real.sin (manuscriptPhaseFn m n θ) + manuscriptError m n hm θ.
```

The public conclusions to prove are:

1. For `θ ∈ [0,π]`, this actual residual has ordinary derivative
   `cos(F θ) * deriv F θ + deriv E θ`, where `F = manuscriptPhaseFn m n`
   and `E = manuscriptError m n hm`.
2. The matrix curve
   `θ ↦ boundaryMatrix m n (characteristicRoots m θ)` is globally
   `ContDiff ℝ ⊤`. Its entries are powers of the previously constructed
   globally smooth nonzero roots; matrix smoothness is not assumed.
3. For `0 < θ ≤ π`, the exact equality is
   `manuscriptBoundaryDeterminant m n θ = manuscriptNormalizer m n θ *
   (manuscriptResidual m n hm θ : ℂ)`.
4. For `0 < θ < π` and `manuscriptResidual m n hm θ = 0`, the actual
   determinant has derivative
   `manuscriptNormalizer m n θ * (deriv (manuscriptResidual m n hm) θ : ℂ)`.
   The identity used for differentiation holds in a neighborhood of θ;
   equality at a single point is not sufficient or assumed sufficient.
5. If additionally `deriv (manuscriptResidual m n hm) θ ≠ 0`, then
   
   ```
   Module.finrank ℂ
     (Module.End.eigenspace
       ((toeplitz m n).map Complex.ofReal).mulVecLin (symbol m θ : ℂ)) = 1.
   ```
6. Under the same hypotheses,
   
   ```
   ∃! j : ℕ, 1 ≤ j ∧ j ≤ n ∧ eigenvalue m n j = symbol m θ.
   ```

The simple-root assumptions in (5) and (6) are premises of this bridge;
existence or uniqueness of a zero in a specified phase cell remains a
separate obligation. The conclusion gives a unique original index for
the value, but does not identify that index with a phase-cell label.
There is no assumption of characteristic-root distinctness, the root
equation, matrix rank, eigenvalue multiplicity, or normalization: the
existing concrete theorems must discharge these properties. The open
interval is required for distinct roots and local differentiation of the
normalized identity; the artificial determinant zero at π is excluded.
The result permits `n = 0`, where the simple-zero premises cannot hold.

The intended proof uses actual Lemma 3, a derivative product rule,
`HasDerivAt.congr_of_eventuallyEq`, `SimpleDeterminant`, and
`EigenvalueMultiplicity`. No new axiom, computation certificate, or
external mathematical dependency is permitted. The author will not run
a compiler; the coordinator owns serialized local testing. This file
does not claim a local build or a GitHub Comparator result.
