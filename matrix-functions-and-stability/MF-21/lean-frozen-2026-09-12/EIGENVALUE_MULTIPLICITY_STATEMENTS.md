# MF-21: the actual sorted list and geometric multiplicity

Statement lock recorded before writing `MF21Restart/EigenvalueMultiplicity.lean`.
The manuscript and `MF21Restart/Definitions.lean` remain unchanged.

For every natural `m,n` and real `lam`, prove

```lean
theorem count_orderedEigenvalueList_eq_complex_eigenspace_finrank
    (m n : ℕ) (lam : ℝ) :
    (orderedEigenvalueList m n).count lam =
      Module.finrank ℂ
        (Module.End.eigenspace
          ((toeplitz m n).map Complex.ofReal).mulVecLin (lam : ℂ))
```

Then prove the precise one-based uniqueness consequence:

```lean
theorem existsUnique_eigenvalue_index_of_complex_eigenspace_finrank_one
    (m n : ℕ) (lam : ℝ)
    (hdim : Module.finrank ℂ
      (Module.End.eigenspace
        ((toeplitz m n).map Complex.ofReal).mulVecLin (lam : ℂ)) = 1) :
    ∃! j : ℕ, 1 ≤ j ∧ j ≤ n ∧ eigenvalue m n j = lam
```

These are the multiplicity implication used in the last sentence of the
manuscript's Lemma 4 root-simplicity paragraph. The list is the actual sorted
Hermitian eigenvalue list from the frozen definitions, including repetitions;
the linear operator is the actual complexified Toeplitz matrix. The bounded
index excludes the accessor's totalized value outside `1..n`.

The first statement assumes neither simplicity nor a characteristic-polynomial
factorization. Its proof must reuse Mathlib's spectral theorem for symmetric
operators, identify its Euclidean-space eigenspace with the ordinary matrix
eigenspace through `WithLp.linearEquiv`, and preserve characteristic-polynomial
root multiplicity under the injective real-to-complex map. Sorting preserves
the multiset. Count one must then imply a unique position in that actual list.

There is no `m ≥ 1` or `n ≥ 1` hypothesis. At `n = 0`, both sides of the first
statement are zero and the second premise is impossible. The second theorem
does not prove dimension one, determinant simplicity, root localization,
index alignment, or the final MF-21 target. No new axioms or numeric oracle
are authorized. Source development here runs no compiler; local testing is
serialized by the coordinator and GitHub Comparator remains a separate check.
