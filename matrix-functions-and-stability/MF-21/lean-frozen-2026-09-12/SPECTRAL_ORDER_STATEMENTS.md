# Spectral order and actual eigenangles: statement lock

This lock precedes `MF21Restart/SpectralOrder.lean`. It supplies the
order and angle facts needed for manuscript Lemma 4 using the unchanged
symbol, sorted list, and one-based eigenvalue accessor.

Prove these exact public conclusions:

```
symbol_zero (m : ℕ) (hm : 1 ≤ m) : symbol m 0 = 0

symbol_pi (m : ℕ) : symbol m Real.pi = (4 : ℝ)^m

symbol_strictMonoOn (m : ℕ) (hm : 1 ≤ m) :
  StrictMonoOn (symbol m) (Set.Icc 0 Real.pi)

orderedEigenvalue_monotone (m n : ℕ) :
  Monotone (orderedEigenvalue m n)

eigenvalue_existsUnique_angle
  (m n j : ℕ) (hm : 1 ≤ m) (hj : 1 ≤ j) (hjn : j ≤ n) :
  ∃! θ : ℝ, θ ∈ Set.Ioo 0 Real.pi ∧
    symbol m θ = eigenvalue m n j
```

The zero endpoint and strict monotonicity require positive order:
at `m=0` the symbol is constantly one. The pi endpoint is valid also
at zero order. Matrix size zero is allowed in the sorted-array order
statement; the actual one-based index premises in the angle theorem
force positive size. No conclusion concerns totalized out-of-range
accessor values. Sorted eigenvalues are nondecreasing; strict ordering
or simplicity of the entire spectrum is not claimed.

The strict symbol order follows from the already proved identity
`symbol m θ=(2-2*cos θ)^m`, strict decrease of cosine on `[0,pi]`,
nonnegativity of the base, and the strict natural-power inequality for
positive exponent. The array order must follow from the actual
`Multiset.sort` definition, with its list indexing intact; no separate
ordered list is substituted.

For every actual indexed eigenvalue, the proved strict spectral
enclosure places it in `(0,4^m)`. Continuity and the two exact endpoint
values give an angle by IVT. Endpoint exclusion gives membership in
`(0,pi)`, and strict symbol monotonicity gives uniqueness. No eigenangle,
inverse-symbol function, root-choice definition, or spectral order is
assumed or added to the trusted definitions.

This component does not identify a phase-window label with an
eigenvalue index or prove any asymptotic expansion. There are no new
axioms, numerical certificates, or literature inputs. The author runs
no compiler; the coordinator owns serialized local tests. No compiler
or Comparator result is claimed by this lock.
