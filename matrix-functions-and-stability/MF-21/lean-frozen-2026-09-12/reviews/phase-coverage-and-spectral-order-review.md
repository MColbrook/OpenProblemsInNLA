# Independent review: phase coverage and actual spectral order

Verdict: **APPROVE** both modules at the exact hashes below. The coverage
theorem rules out gaps and the artificial final phase window for every
sufficiently high actual residual zero. The spectral-order module proves
the nondecreasing order of the unchanged sorted spectrum and the unique
interior angle of each in-range original one-based eigenvalue. Neither
module assumes its spectral or phase conclusion.

Reviewer: `/root/mf21_restart_lean_audit`, 20 September 2026. These two
modules were authored by `/root/mf21_restart_manuscript`; the reviewer
made no source edits and launched no compiler. This report follows the
pinned referee standards, SHA256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Exact sources and actual local evidence

| Artifact | SHA256 |
|---|---|
| `MF21Restart/PhaseRootCoverage.lean` | `89f61e946010850d0cc6de3052457ece34233e9c079f021172c23e0ff0d28d1c` |
| `PHASE_ROOT_COVERAGE_STATEMENTS.md` | `331eb7fe1824eff36e9281924921eabca2c4c042e5775bdcb9cd54e59342d6fb` |
| `evidence/logs/phase-root-coverage-01.json` | `f01f68d02274cd0121c13bb2ba6184e8f4fe8be71a782738559e64cd1706b4a7` |
| `evidence/logs/phase-root-coverage-01.log` | `a41478e3d2b7b71522fbe5eb1f1d63f63eef2993c64a0ddabfa1558e8225a42a` |
| `.lake/build/lib/lean/MF21Restart/PhaseRootCoverage.olean` | `daa1b1ed2d89310ab4d419766ccdc373d201dc1c3bb9b1c648be39aeb294d783` |
| `MF21Restart/SpectralOrder.lean` | `e2a65362fe207b91b8602ce7ec6e85c7e9dacb9d59ce547a9e351f3372ddb468` |
| `SPECTRAL_ORDER_STATEMENTS.md` | `9f6a15a0d57025238f9427506b5c8dab5da72fa089358f9fc5851eeccabe324a` |
| `evidence/logs/spectral-order-01.json` | `7401fdb1632be10c3d73969bb0a4704337388cba0cd649ffd478683056214b26` |
| `evidence/logs/spectral-order-01.log` | `3d11ea66d1d868266a8269521ee3fe7f6a6ee25c8962e010a82428690098cf0b` |
| `.lake/build/lib/lean/MF21Restart/SpectralOrder.olean` | `aaac609b05a407b2b306206629a9b50a7155d79dbcb9c840c759047de8d497eb` |

The reviewer recomputed every listed hash and matched both actual 01
records to the current source, log, and compiled output. Each records
`exit_code=0`, `source_unchanged=true`, `LEAN_NUM_THREADS=1`, and command
`lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/<Module>.olean
MF21Restart/<Module>.lean`. Coverage has one printed axiom report and
SpectralOrder five; all contain only `propext`, `Classical.choice`, and
`Quot.sound`. Both logs contain no error or missing-proof warning. These
are actual local Lean results. No Comparator or GitHub run is asserted.

The unchanged manuscript `original-proof/solution.md` has SHA256
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`.
Relevant source passages are lines 219 and 237–249. The exact one-based
accessor and sorted list remain `Definitions.lean:38–53`.

## Coverage findings

1. **Exact uniform quantifiers and domain.**
   `manuscriptResidual_high_phase_root_coverage`, lines 70–76, agrees
   literally with the lock. For each m>=2, fixed N,J>=1 work for every
   n>=N and every theta strictly between 0 and pi. The phase threshold
   is the closed lower boundary `J*pi-pi/4`; the conclusion has the
   closed quarter-period cell with `J<=k<=n`. It has no assumed error,
   phase monotonicity, derivative bound, or root-label correspondence.
   The residual-zero premise is the intended object being located, not
   a contradictory surrogate limit or an assumed conclusion.

2. **Nearest-integer indexing is exact and safe at the lower cutoff.**
   Lines 17–50 choose `floor_Nat(x/pi+1/2)`. The input lower bound gives
   `x/pi>=J-1/4`, hence the floor argument is at least J and nonnegative.
   The upper bound `x<=(n+1)*pi` implies the chosen natural index is at
   most n+1. The two floor inequalities give distance at most pi/2.
   Thus natural-floor truncation does not silently relabel negative
   phases or lose k=J. Equality at a nearest half-period is permitted.

3. **The half-cell to quarter-cell inference uses the correct sine
   branch.** Lines 54–68 first compare the nonnegative absolute phase
   offset, bounded above by pi/2, with pi/4. The library absolute-sine
   identity and the exact shift by a natural multiple of pi reduce
   its sine to `|sin x|`. The existing strict margin
   `sin(pi/4)>1/4` contradicts `|sin x|<1/4` outside the quarter-cell.
   There is no inverse-sine branch assumption or argument-of-product
   substitution. The already tested kernel-mode LeanCert margin in
   `Numerics.lean:10–19` is reused; this module adds no computation.

4. **The actual estimates discharge all helper premises.** Lines
   77–96 choose the maxima of the actual eventual phase-monotonicity
   and final-window thresholds, retain the actual high-phase J, use
   `F(pi)=(n+1)*pi`, and use `H=sin(F)+E=0` to obtain
   `|sin(F)|=|E|<1/4`. Lines 98–105 eliminate only k=n+1 by the
   proved interior final-window exclusion. Theta=pi is excluded in the
   public domain, so the artificial endpoint zero is not incorrectly
   declared nonzero. No premise asserts that only n eigenvalues exist
   or identifies k with an ordered index.

## Spectral-order findings

1. **The symbol and endpoint conventions are unchanged.** Lines
   17–31 derive zero at theta=0 for m>=1, the value 4^m at pi for all
   m, and strict increase on the whole closed interval for m>=1 from
   `(2-2*cos(theta))^m`. Nonnegative bases and the nonzero exponent
   are justified. At m=0 the symbol is identically one; strict order
   and the zero-endpoint assertion correctly exclude that case.

2. **Sorted values are nondecreasing, with all multiplicities kept.**
   Lines 35–43 use `Multiset.pairwise_sort` on the literal
   `orderedEigenvalueList`, then the list's indexed order theorem.
   They do not substitute an abstract ordered array or assert global
   simplicity. The theorem allows n=0; its `Fin 0` domain is naturally
   empty, rather than hiding a positive-size hypothesis needed later.

3. **Angles correspond to original one-based eigenvalues.** Lines
   47–71 retain explicit `1<=j<=n`; these force positive matrix size
   and exclude the accessor's totalized out-of-range zero. The actual
   strict enclosure `(0,4^m)` supplies IVT membership, both endpoint
   inequalities exclude theta=0,pi, and the actual symbol's strict
   monotonicity gives uniqueness. Repeated eigenvalues would have the
   same angle at multiple indices; this theorem does not falsely
   exclude them. The largest index j=n is included.

## Trust, independence and limits

Recursive project-import scans covered 53 files for PhaseRootCoverage
and five for SpectralOrder, including each root module, with no
`sorry`, `admit`, custom `axiom`, `unsafe`, or `native_decide` marker.
Neither closure imports `Challenge.lean` or an assumed Target. The five
deliberate Challenge placeholders remain outside these proof closures.
This report independently reviews the two named modules, their types,
and their uses of existing APIs. It does not reclassify any helper
written by this reviewer as independently reviewed.

These results establish coverage and order needed for the subsequent
indexing proof; they do not themselves identify a phase label with its
sorted eigenvalue index, prove the quantitative error in (19), build Y,
or complete the original MF-21 Target. No complete-target count changes.
No material correctness or fidelity issue was found.
