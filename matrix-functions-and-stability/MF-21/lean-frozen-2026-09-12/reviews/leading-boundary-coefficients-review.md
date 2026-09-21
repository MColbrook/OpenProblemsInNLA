# Independent review: leading Laplace coefficients

Verdict: **APPROVE** the five exact intermediate results in the successfully
compiled frozen source. The full MF-21 Target and Comparator are outside this
approval.

Reviewer: `/root/mf21_restart_lean_audit`, 20 September 2026, following the
pinned referee standards (SHA256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`).
The source was authored by `/root/mf21_restart_manuscript` with coordinator
elaboration fixes. This reviewer did not edit it or run Lean.

## Frozen source and evidence

| Artifact | SHA256 |
|---|---|
| `MF21Restart/LeadingBoundaryCoefficients.lean` | `f048a547bf8493c0355996d766e69562be5454bd0545ed4cb875e7dd957b7ab0` |
| `LEADING_BOUNDARY_COEFFICIENTS_STATEMENTS.md` | `9b881e2856061043e3e52e0b1d8621d29f82ed29f712d007815b1fc5e5187e57` |
| `evidence/logs/leading-boundary-coefficients-05.json` | `7a8b559b23c12c4da12d3beffc97e5561e78abbbd91e969771a61608c85c4f9e` |
| `evidence/logs/leading-boundary-coefficients-05.log` | `052bb462e9120b93352dbe5f568d49b33caf0584b7a6220d741493238d3c4e7b` |
| `.lake/build/lib/lean/MF21Restart/LeadingBoundaryCoefficients.olean` | `fb2163d70d468451a032207ef10750934e879b9d5be571f64eee7e098e141e54` |

All hashes were recomputed. The execution record's source, log, and output
hashes all match. The actual local command was `lake env lean -j1 -M4096 -o
.lake/build/lib/lean/MF21Restart/LeadingBoundaryCoefficients.olean
MF21Restart/LeadingBoundaryCoefficients.lean`, with `LEAN_NUM_THREADS=1`,
exit_code=0 and source_unchanged=true. Its five axiom reports use only
`propext`, `Classical.choice`, and `Quot.sound`. The remaining log messages
are simplifier/tactic-style suggestions, not proof failures.

The initial 01 run was an actual failure, source SHA256
`95a67aa0febaf49c10147a2ea8f0d7f6cc382909a50e2e191bab9bf852917d8a`.
Its two coefficient reports contained compiler-generated `sorryAx` after
elaboration errors. Those reports are not successful evidence and are not
used here. The reviewed 05 version replaces the problematic dependent
`Fin.snoc` calc with the same proved interval-product rewrite and uses an
explicit definitional `change` for the minus phase product. The mathematical
statements and lock are unchanged.

## Exact mathematical checks

The source is compared to frozen `original-proof/solution.md:161–189`,
particularly (15), SHA256
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`.
The determinant coefficient convention is
`BoundaryExpansion.lean:255–270`, SHA256
`bc873ac5a5cb569d3dda0bc3b6ecf623e09d326f0d82cd613fdc3149c24a3979`.

- `LeadingBoundaryCoefficients.lean:19–59` proves prepend and append
  Vandermonde identities from the actual product of differences. Prepending
  u gives factors `v_i-u`; appending u gives `u-v_i`. These orientations are
  essential and are correct. In the append proof the last index's upper
  interval is empty, and each earlier upper interval adds exactly the last
  factor. No extra reversal or determinant sign is introduced.

- Lines 61–98 factor the append/prepend products as
  `V(R) u^(m-1) product(1-r/u)` and
  `Q product(1-r*u) V(O)`. Division by u is justified by a real proof of its
  nonzero complex value. Each reciprocal stable root is also proved nonzero.
  Q is rewritten using the exact exterior-root product theorem, not assumed
  to equal a convenient expression.

- Lines 100–121 prove `product(1-r*z)=conj(f)` by conjugating the actual
  factors and reversing the stable indices. Conjugation of z-inverse is z
  for every real theta. Reindexing the finite product is valid without
  nonvanishing assumptions. The proof uses no principal argument of a
  product and makes no phase-branch substitution.

- Lines 123–214 derive all four root tuples from the increasing finite-set
  enumerations: Splus=(z,O), its complement=(R,z-inverse),
  Sminus=(z-inverse,O), and its complement=(R,z). These are equalities of
  actual root-valued tuples, not extra tuple hypotheses. The `ell+1` and
  exterior `index-m` shifts agree. The supporting inherited-index and sign
  file has SHA256
  `cccc3c1efd31bcd7a7bb3c9e7f63b6414f79537098ca4ee7885ce613df02833c`
  and was independently inspected in
  `reviews/boundary-conjugation-normalizer-review.md`.

- Lines 217–257 prove the precise coefficients
  `-V(R)V(O)Q (z-inverse)^(m-1) conj(f)^2` and
  `+V(R)V(O)Q z^(m-1) f^2`. Thus the first sign is sigma=-1 in manuscript
  (15), with the second sign its negative. Both factors have Q to the first
  power and f or conjugate(f) squared. The coefficient theorem's complement
  Vandermonde precedes the selected Vandermonde; commutativity in complex
  scalars permits the displayed order without another sign. As a small
  orientation check, m=2 gives Splus={1,3}, with coefficient
  `-(z-inverse-r)*(q-z)`, exactly the claimed expression.

- Lines 259–279 identify the selected root products as z*Q and z-inverse*Q
  from the actual insert definitions. The inserted oscillatory index is
  proved absent from the exterior set, so there is no duplicated product
  factor or hidden cardinality adjustment.

The main coefficient and selected-product theorems assume only m>=2 and a
real theta; conjugate-product equality has no m lower bound. At theta=0 or
pi, the identities remain polynomial/product identities even when roots
coincide. No invalid full-root injectivity, nonzero Vandermonde, or nonzero
coefficient premise is used at those endpoints.

## Scope and trust

No material mismatch with the lock or manuscript was found. There are no
custom axioms, `sorry`, `admit`, unsafe declarations, or native evaluation
shortcuts in the reviewed source. The proof uses symbolic finite-product
algebra and existing determinant APIs; it does not enumerate dimensions or
use numerical verification.

This review accepts the five new results and the local proof steps producing
them. It does not independently review this reviewer's own imported
`PhaseProduct`, root-list construction, or root-symmetry sources. Their
interfaces are read as existing dependencies, with source-matched local
evidence handled separately.

The module does not yet assemble the two leading determinant terms into
`N*sin(F)`, identify the nonleading sum with D/N-sin(F), prove error reality
or endpoint cancellation, or establish the MF-21 Target. Those tasks are
not hypotheses smuggled into these identities. No completed original target
is counted, and no GitHub Comparator run is reported.
