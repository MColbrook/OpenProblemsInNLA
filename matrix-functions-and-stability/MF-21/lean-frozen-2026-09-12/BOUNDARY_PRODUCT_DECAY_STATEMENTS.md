# Actual subset-product decay: statement lock

Recorded before writing `MF21Restart/BoundaryProductDecay.lean`.
This is the product-modulus argument in unchanged manuscript (17), using
the actual ordered characteristic roots. It leaves coefficient/Vandermonde
normalization to a separate module.

Use these agreed definitions:

```lean
def boundaryExteriorIndices (m : ℕ) : Finset (Fin (2 * m)) :=
  Finset.univ.filter (fun i => m < i.val)

def boundaryLeadingZIndices (m : ℕ) (hm : 1 ≤ m) : Finset (Fin (2 * m)) :=
  insert ⟨m - 1, by omega⟩ (boundaryExteriorIndices m)

def boundaryLeadingZInvIndices (m : ℕ) (hm : 1 ≤ m) : Finset (Fin (2 * m)) :=
  insert ⟨m, by omega⟩ (boundaryExteriorIndices m)

def boundaryExteriorProduct (m : ℕ) (θ : ℝ) : ℂ :=
  ∏ i ∈ boundaryExteriorIndices m, characteristicRoots m θ i

def boundaryProductRatio (m : ℕ) (θ : ℝ) (S : Finset (Fin (2 * m))) : ℂ :=
  (∏ i ∈ S, characteristicRoots m θ i) / boundaryExteriorProduct m θ
```

Prove that `boundaryExteriorProduct m θ` and `boundaryProductRatio m θ S`
are nonzero for all m, θ, S. For m≥2 prove the actual ratio is smooth on
the real line for each S, using actual finite products and the proved
nonvanishing denominator.

The main target is:

```lean
theorem boundaryProductRatio_uniform_exp_decay (m : ℕ) (hm : 2 ≤ m) :
    ∃ c : ℝ, 0 < c ∧
      ∀ S : Finset (Fin (2 * m)), S.card = m →
        S ≠ boundaryLeadingZIndices m (by omega) →
        S ≠ boundaryLeadingZInvIndices m (by omega) →
        ∀ θ : ℝ, 0 ≤ θ → θ ≤ Real.pi →
          ‖boundaryProductRatio m θ S‖ ≤ Real.exp (-c * θ)
```

The constant must come from `stable_roots_uniform_exp_decay` and is
independent of both S and θ. Neither the target estimate nor a root-product
inequality may be assumed. Prove the finite combinatorial fact that a
nonleading m-element subset either selects a stable root or omits an exterior
root. Cancellation of the selected exterior factors gives the exact product
of selected nonexterior roots and reciprocals of omitted exterior roots.
Every such norm factor is at most one, and at least one is an actual stable
root norm bounded by the proved common exponential estimate. Thus the proof
also justifies the manuscript's intermediate bound by one stable root norm.

The interval includes zero: the claimed estimate there is non-strict and
both sides equal one. It includes π: the two unit-root values coincide but
the two leading subsets remain different index sets; full root-list
injectivity is not needed for this modulus argument. The leading subsets
are excluded by index identity, not by potentially coincident root values.
The natural m≥2 premise covers the manuscript's m≥3 domain.

Auxiliary cardinality, nonleading-witness, and exact cancellation statements
may be exposed for reuse. This task does not prove Q is real positive, the
leading coefficient signs, the real normalized determinant, derivative
bounds for the ratios, or any bound for the normalized coefficients. It does
not count as a completed original target. No new axioms, numerical oracle,
compiler process, or edits to frozen sources are authorized here.
