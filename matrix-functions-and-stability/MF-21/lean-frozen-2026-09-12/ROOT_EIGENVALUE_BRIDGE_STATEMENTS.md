# Real and complex eigenvalues: statements before proof

Locked on 20 September 2026, before writing `RealComplexEigenvalue.lean`.
This supplies the missing scalar-field bridge between the exact boundary
determinant criterion following manuscript equation (13) and the original
one-based ordered real eigenvalue accessor.

First prove, for every natural `n`, every real matrix
`A : Matrix (Fin n) (Fin n) ℝ`, and every `lam : ℝ`:

```lean
theorem real_matrix_charpoly_root_iff_complex_eigenvector
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ) :
    A.charpoly.IsRoot lam ↔
      ∃ v : Fin n → ℂ, v ≠ 0 ∧
        A.map Complex.ofReal *ᵥ v = (lam : ℂ) • v
```

Use the injective real-to-complex ring homomorphism, compatibility of
characteristic polynomials with coefficient maps, and the proved Mathlib
equivalence between characteristic roots and nonzero eigenvectors.
No Hermitian or nonempty-dimension hypothesis is needed. No scalar-field
equivalence, kernel correspondence, eigenvector, or characteristic-root
condition may be assumed as an extra premise. The `n=0` case has neither
a characteristic root nor a nonzero vector.

Then specialize and compose with the existing exact bridges:

```lean
theorem eigenvalue_index_iff_boundaryDeterminant_zero
    (m n : ℕ) (hm : 1 ≤ m) (lam : ℝ) (w : Fin (2 * m) → ℂ)
    (hinj : Function.Injective w) (hnonzero : ∀ i, w i ≠ 0)
    (hvalue : ∀ i, (2 - w i - (w i)⁻¹) ^ m = (lam : ℂ)) :
    (∃ j : ℕ, 1 ≤ j ∧ j ≤ n ∧ eigenvalue m n j = lam) ↔
      (boundaryMatrix m n w).det = 0

theorem mem_orderedEigenvalueList_iff_boundaryDeterminant_zero
    (m n : ℕ) (hm : 1 ≤ m) (lam : ℝ) (w : Fin (2 * m) → ℂ)
    (hinj : Function.Injective w) (hnonzero : ∀ i, w i ≠ 0)
    (hvalue : ∀ i, (2 - w i - (w i)⁻¹) ^ m = (lam : ℂ)) :
    lam ∈ orderedEigenvalueList m n ↔
      (boundaryMatrix m n w).det = 0
```

These statements use exactly the unchanged integral-defined `toeplitz`,
its actual sorted Hermitian eigenvalue list, and the concrete boundary
matrix. The bounded natural accessor must include both `j=1` and `j=n`
and must not admit its totalized value outside `1 ≤ j ≤ n`.

The root-list hypotheses are exactly those of the previously proved
`BoundaryToeplitz` criterion, with a real spectral parameter cast into ℂ.
The list is still supplied: construction and smoothness of the manuscript's
particular roots, endpoint coalescence, and quantitative root estimates
remain separate obligations. No multiplicity, equality of kernel
dimensions, phase ordering, asymptotic expansion, or MF-21 Target theorem
is claimed here. These bridge corollaries are not separate original
problem completions.

Only this new statement document and proof module may be edited for this
task. The author does not run Lean; the coordinator records serial local
compilation and any eventual GitHub Comparator checks separately.
