# Kernel dimension and determinant derivative: statement first

This lock precedes `MF21Restart/DeterminantMultiplicity.lean`. It supplies
the general matrix-curve fact used in manuscript Lemma 4: if the complex
kernel at a point has dimension at least two, the derivative of the
complex determinant along a differentiable real-parameter curve is zero.
Only differentiability at that point is needed. No boundary-matrix or
eigenspace equivalence is part of this task.

The precise public statements are:

```lean
theorem det_updateRow_eq_zero_of_two_le_finrank_ker
    (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ)
    (hker : 2 ≤ Module.finrank ℂ (LinearMap.ker A.mulVecLin))
    (i : Fin N) (b : Fin N → ℂ) :
    (A.updateRow i b).det = 0

theorem hasDerivAt_det_curve
    (N : ℕ) (M : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (M' : Matrix (Fin N) (Fin N) ℂ) (θ : ℝ)
    (hM : HasDerivAt M M' θ) :
    HasDerivAt (fun t : ℝ => (M t).det)
      (∑ i : Fin N, ((M θ).updateRow i (M' i)).det) θ

theorem hasDerivAt_det_zero_of_two_le_finrank_ker
    (N : ℕ) (M : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (M' : Matrix (Fin N) (Fin N) ℂ) (θ : ℝ)
    (hM : HasDerivAt M M' θ)
    (hker : 2 ≤ Module.finrank ℂ (LinearMap.ker (M θ).mulVecLin)) :
    HasDerivAt (fun t : ℝ => (M t).det) 0 θ

theorem hasDerivAt_det_zero_of_entrywise_deriv_and_two_le_finrank_ker
    (N : ℕ) (M : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (M' : Matrix (Fin N) (Fin N) ℂ) (θ : ℝ)
    (hM : ∀ i j, HasDerivAt (fun t : ℝ => M t i j) (M' i j) θ)
    (hker : 2 ≤ Module.finrank ℂ (LinearMap.ker (M θ).mulVecLin)) :
    HasDerivAt (fun t : ℝ => (M t).det) 0 θ
```

The dimension is over **ℂ**, not ℝ. This distinction matters: the curve
`diag(t,1)` at zero has a real kernel of dimension two but a nonzero
determinant derivative. Its complex kernel has dimension one, so it
does not satisfy the locked hypothesis. For `N=0` or `N=1`, the complex
dimension hypothesis is impossible; no separate size assumption is
necessary. For `N≥2` the hypothesis is realized, for example, by the zero
matrix at the point.

The planned derivation uses existing proved Mathlib infrastructure:

1. Package the actual `Matrix.detRowAlternating.toMultilinearMap` with
   the existing determinant continuity theorem. Apply
   `ContinuousMultilinearMap.hasFDerivAt` and `linearDeriv_apply`, restrict
   the complex derivative to real scalars, and use the chain rule. This
   proves the exact row-replacement derivative formula above; it is not
   assumed as a premise or supplied as an axiom.
2. Restrict the new row's dot-product functional to `ker A`. Its codomain
   has complex dimension one, so
   `LinearMap.ker_ne_bot_of_finrank_lt` produces a nonzero vector in
   its kernel. That vector is killed both by A and by the replacement
   row. `Matrix.updateRow_mulVec` and the actual determinant/kernel
   criterion imply that every row-replacement determinant is zero.
3. Sum those zero terms and, for the entrywise form, assemble the two
   finite Pi derivatives using `hasDerivAt_pi`.

No adjugate-vanishing condition, cofactor estimate, determinant derivative,
or rank bound equivalent to the conclusion is added as a hypothesis. No
claim about the multiplicity of a spectral eigenvalue, equality of kernel
dimensions, ordering of roots, or the complete MF-21 target is made.

Validation policy: this author does not run Lean. The coordinator keeps
the serialized local command and output evidence; local execution and any
eventual GitHub Comparator result must be reported separately.
