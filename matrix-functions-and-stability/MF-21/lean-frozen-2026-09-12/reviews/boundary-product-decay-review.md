# Independent actual subset-product decay review

Verdict: **APPROVE**, for the definitions, finite combinatorics, exact
cancellation, and six printed results in `BoundaryProductDecay.lean`.
This proves manuscript (17)'s actual complex product-ratio modulus bound,
uniform in the nonleading subset and theta, including both endpoints.
It does not prove that the ratios are real-valued, that Q is positive
real, or that the normalized determinant error satisfies its derivative
estimate.

Reviewer: `/root/mf21_restart_lean_audit`, 20 September 2026. I did not
author or edit this module, including the coordinator's moved leading-set
helpers and elaboration fixes. I independently read its full frozen source,
statement lock, the actual root definitions and decay inputs, and the
unchanged manuscript. My own imported characteristic-root infrastructure
is not independently reapproved by this report. I ran no compiler. The
referee standard has SHA-256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Exact inspected artifacts

Paths are relative to `MF21-restart`.

| Path | SHA-256 |
| --- | --- |
| `MF21Restart/BoundaryProductDecay.lean` | `f9f9b6b0d5c8b8842049f91850a3cb6d4482747443c1448d1c1e325bdcd0d0e3` |
| `BOUNDARY_PRODUCT_DECAY_STATEMENTS.md` | `98a4a675f7db605a74978c1354e632d6926540c4ebf2eb3f823739eeca6afab1` |
| `MF21Restart/StableRootBounds.lean` | `de3a7eb721977af0be836dff1f6c68b525db5dccd36f5e6b4a68075633052b31` |
| `MF21Restart/StableRootDecay.lean` | `edb5b83593d2d7a8dc43e20ec4c77909a8c49662218342683d5e2f1d89911bb2` |
| `original-proof/solution.md` | `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa` |
| `evidence/logs/boundary-product-decay-02.json` | `1a404a55f791940c3241b09aa11855d2df6a0f92cf9a164c35190b7ffc9d44d1` |
| `evidence/logs/boundary-product-decay-02.log` | `0f30d792b8d000fc99380773305ddd6e32e7600cbdf00b895583f06ea529e77d` |
| `.lake/build/lib/lean/MF21Restart/BoundaryProductDecay.olean` | `bb59f48610ac7efa27362d523ce20eec9640bed8f6cb3615ce4eec7719c5fb14` |

The retained record reports an actual local run from
`2026-09-20T20:51:59.386605+00:00` to
`2026-09-20T20:52:13.562525+00:00`, command

```text
lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/BoundaryProductDecay.olean MF21Restart/BoundaryProductDecay.lean
```

with exit code 0 and unchanged source. I independently rehashed source,
log, and output; each exactly matches the corresponding recorded hash.
All six printed declarations report only `propext`, `Classical.choice`,
and `Quot.sound`. The warnings concern an unnecessary final simp after
`convert!`; they do not add a proof obligation or trust assumption. No
GitHub Comparator result is claimed.

## Literal sets, products, and nonvanishing

Lines 22–35 use the actual ordered characteristic roots. The exterior
index set is precisely `m<i<2*m`; the two distinguished sets add index
`m-1` (z) or index m (z inverse). Thus the denominator is the product
of exactly q_1 through q_(m-1), and the ratio is literally
`prod_{i in S} w_i / Q`, as in (17), `solution.md:193–200`.

The index set cardinality at lines 42–50 uses the open upper interval
after index m and gives m−1. Lines 52–70 prove that the z-leading set
has cardinality m and contains the z position while excluding the
inverse-z position. These are genuine finite-set identities, meaningful
also at m=1, rather than hypotheses asserting the desired combinatorics.

Lines 72–82 prove Q and every product ratio nonzero for all real theta
from nonvanishing of each actual characteristic root. Lines 84–96 prove
the actual finite products and quotients are globally real analytic for
m>=2, using their proved nonzero denominator. This does not assume Q
is positive, bounded, or real. The quotient itself is **complex-valued**;
the later estimate concerns its real norm.

## Nonleading witness and cancellation

Lines 101–144 derive the key combinatorial alternative for a subset of
cardinality m. If it selects no stable index and omits no exterior index,
it contains all m−1 exterior indices. Its difference from that set has
cardinality exactly one. The remaining index is neither stable nor
exterior, so it must be z or inverse z, and the whole subset is one of
the two excluded leading sets. This proves, without an assumption about
product norms, that a nonleading subset selects a stable index or omits
an exterior one.

This argument uses index identities throughout. It remains valid when
root values coincide at theta=0 or theta=pi. It does not invoke full
root-list injectivity at either excluded endpoint of that theorem.

Lines 148–163 split both numerator and denominator over their common
selected exterior factors. Their product is nonzero by actual root
nonvanishing, justifying cancellation. The resulting expression is
exactly the product of selected nonexterior roots times reciprocals of
omitted exterior roots. Lines 165–170 take norms using multiplicativity.
No exterior root is incorrectly estimated by one: only its reciprocal,
which is the actual stable root, appears after cancellation.

## Uniform constant and closed-interval estimate

The main theorem at lines 180–186 has a single positive c chosen before
both S and theta. The source at line 188 obtains it from the actual
`stable_roots_uniform_exp_decay`. I inspected that input: it takes the
minimum of the finitely many positive root constants, with m>=2 ensuring
the finite family is nonempty, and proves the bound for every published
stable index and all theta in `[0,pi]`. There is no n-dependence or
subset-dependent constant hidden in the quantifier order.

Lines 191–214 show that every selected nonexterior norm is at most one:
stable roots use the common exponential bound, and both unit roots have
norm one. The reciprocal of any omitted exterior root is exactly a
stable root and satisfies the stronger `exp(-c*theta)` bound. The real
exponential is at most one because c>0 and theta>=0.

The private finite-product inequality at lines 172–178 bounds a product
of nonnegative factors at most one by any one selected factor. Lines
217–252 use the combinatorial witness to select a factor with the
strong exponential bound; the other product is nonnegative and at most
one. Both alternatives are handled, with the correct direction for
each real multiplication inequality.

At theta=0, all roots equal one, Q=1, and both sides of the conclusion
are one. The theorem correctly gives a non-strict inequality. At
theta=pi, z and its inverse have the same value −1, but the two leading
subsets remain distinct index sets. Every nonleading subset still has
the necessary selected-stable or omitted-exterior witness, so its bound
is strictly below one. No endpoint is silently removed or added.

## Trust and remaining scope

The exact definitions and main theorem match the statement lock. The
m>=2 premise covers the manuscript's m>=3 domain and avoids an empty
stable family. The finite combinatorial helper also correctly handles
m=1, where there are no nonleading cardinality-one subsets. This
natural degenerate case does not make the main result vacuous.

No `sorry`, `admit`, custom axiom, unsafe shortcut, `native_decide`,
Challenge import, legacy import, numeric certificate, or enumeration
appears. There is no material correctness, hypothesis-strengthening,
indexing, or source-fidelity finding.

The module proves the actual modulus-decay ingredient. Reality and
positivity of Q, leading-coefficient signs, the reality of the normalized
determinant, uniform logarithmic-derivative bounds for these ratios,
and the finite-sum determinant error estimates remain separate. No
complete MF-21 Target or additional completed original problem is claimed.
