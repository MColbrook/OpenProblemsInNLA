# Statement lock: actual phase label equals the published eigenvalue index

Locked before writing `MF21Restart/PhaseWindowIndexing.lean` on
20 September 2026. The original symbol, matrix, eigenvalue list, phase,
and residual remain unchanged. This is the actual top-down indexing
step in manuscript Lemma 4, not an assumed labelling convention.

Prove exactly:

```lean
theorem eigenvalue_eventual_phase_window (m : ℕ) (hm : 2 ≤ m) :
    ∃ N J : ℕ, 1 ≤ N ∧ 1 ≤ J ∧
      ∀ n : ℕ, N ≤ n → ∀ j : ℕ, J ≤ j → j ≤ n →
        ∃ θ : ℝ, θ ∈ Set.Ioo 0 Real.pi ∧
          symbol m θ = eigenvalue m n j ∧
          |manuscriptPhaseFn m n θ - (j : ℝ) * Real.pi| ≤ Real.pi / 4 ∧
          manuscriptResidual m n hm θ = 0 ∧
          deriv (manuscriptResidual m n hm) θ ≠ 0
```

The thresholds depend only on m. The label in the phase window is the
same natural j used by the original one-based accessor. The angle is
the unique interior angle of that eigenvalue by the already proved
strict monotonicity/unique-angle theorem; no second angle convention
is introduced. The residual derivative conclusion gives the simplicity
input already related to actual eigenvalue multiplicity.

Choose J as the maximum of the root-window and high-phase-coverage
cutoffs. Choose N to dominate their matrix-size thresholds, the actual
phase-monotonicity threshold, and J. For a fixed n>=N, choose the unique
root locally for each label in J,...,n, with an arbitrary default only
outside that range. Define its value b(k) using the actual symbol.
Nothing is added to the shared trusted definitions.

Discharge the four hypotheses of `ordered_tail_index` concretely:

1. The array is `orderedEigenvalue m n`, whose monotonicity is proved
   from the existing sorted list by `SpectralOrder`.
2. Distinct natural phase labels have separated closed pi/4 windows;
   the phase value in an earlier cell is strictly smaller. Actual
   strict phase monotonicity orders the chosen angles, and strict
   symbol monotonicity orders their values b(k).
3. Every chosen root has nonzero actual residual derivative. Use
   `ActualSimpleRoots` to obtain its unique original one-based index,
   and translate this exactly to a unique `Fin n` array position.
4. For every array value at least b(J), use the actual unique-angle
   theorem and symbol monotonicity to put its angle at or above the
   chosen J-root. Phase monotonicity puts its phase above the coverage
   threshold, and the actual eigenvalue/residual criterion makes it
   a residual zero. `PhaseRootCoverage` supplies a cell label. If its
   label were below the combined J, separated phase cells would force
   its phase strictly below that of the J-root, a contradiction.
   Its label is therefore in J,...,n, where cell-root uniqueness
   identifies it with the chosen family.

The finite counting theorem now proves that b(j) is at zero-based
position j-1. The existing `eigenvalue_in_range` identity translates
this to the published one-based `eigenvalue m n j`; this translation
must be explicit. No assumption about the number or simplicity of low
eigenvalues is made, and all multiplicities in the sorted array remain.

Private index-translation and separated-cell helpers are permitted.
Every spectral, root, coverage, and order premise of the finite counting
lemma must be discharged from actual compiled project theorems. No
desired labelling, boundary matrix condition, or limiting estimate may
be assumed. The roots' distances from exact phase-grid preimages and
the exponential angle/error bounds in (19) and (25) remain later steps;
this theorem alone does not complete Lemma 4 or MF-21.

The author runs no compiler and edits no existing passed or queued
module. The coordinator owns source-matched local serial tests with
one thread and 4096 MiB. Comparator remains a separate final check.
