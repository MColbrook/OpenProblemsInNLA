# Statement lock: finite ordered-tail counting

Locked before writing `MF21Restart/OrderedTailCounting.lean` on
20 September 2026. This is the finite combinatorial step in the
manuscript's top-down indexing argument, after the analytic root and
coverage statements. It does not assume the desired index equality.

For a finite nondecreasing array `a : Fin n -> alpha` in a linear order
and tail values `b : Nat -> alpha` labelled by J,...,n, prove exactly:

```lean
theorem ordered_tail_index
    {α : Type*} [LinearOrder α]
    (n J : ℕ) (hJ : 1 ≤ J) (hJn : J ≤ n)
    (a : Fin n → α) (b : ℕ → α)
    (ha : Monotone a)
    (hb : StrictMonoOn b (Set.Icc J n))
    (hocc : ∀ k ∈ Set.Icc J n, ∃! i : Fin n, a i = b k)
    (hcover : ∀ i : Fin n, b J ≤ a i →
      ∃ k ∈ Set.Icc J n, a i = b k) :
    ∀ k : ℕ, ∀ hJk : J ≤ k, ∀ hkn : k ≤ n,
      a ⟨k - 1, by omega⟩ = b k
```

The conclusion uses the literal zero-based position k-1 for the
one-based label k. Values below b(J) may repeat and are otherwise
unrestricted: no global strict monotonicity or simplicity is assumed.
Each tail value must occur exactly once. Upper-tail coverage concerns
every array position with value at least b(J), not merely values already
known to be labelled roots. Both requirements are needed for counting
multiplicity rather than just distinct spectral values.

Proof plan: fix a label k and its unique occurrence p. There is a
bijection between the natural labels in Icc(k,n) and array positions
in Ici(p). Send a label to its unique occurrence. Strict ordering of
the labelled values and monotonicity of a put every such occurrence
at or above p and give injectivity. For any array position at or above
p, monotonicity gives a value at least b(k), hence at least b(J), so
coverage supplies a tail label. Strict ordering forces that label to
be at least k, and uniqueness gives surjectivity. Therefore

```
n + 1 - k = card(Icc k n) = card(Ici p) = n - p.val.
```

Since 1<=k<=n and p.val<n, natural arithmetic gives p.val=k-1.
Use the existing Mathlib `Finset.card_bij`, `Nat.card_Icc` and
`Fin.card_Ici`; no new sorting infrastructure or enumeration is needed.
The proof uses only a linear order on the values, so no real arithmetic
or spectral properties are hidden in this combinatorial lemma.

In the eventual MF-21 application, `a` will be the actual sorted
eigenvalue array and b(k) the value of the unique root in the k-th phase
cell. Actual phase-window geometry and strict monotonicity of the
symbol must give strict ordering of b. The concrete simple-root bridge
must give each unique occurrence; the actual spectral enclosure and
PhaseRootCoverage must give upper-tail coverage. All these application
obligations remain explicit and separate. This lemma alone does not
establish index=k for MF-21 or complete the target.

The source author runs no compiler. The coordinator controls local
serial tests with one thread and 4096 MiB. GitHub Comparator remains
a separate final check.
