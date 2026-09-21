# Independent review: dominated spectral trace passage

Verdict: **APPROVE** for this conditional passage. Reviewed on 20 September
2026 by the Lean-audit agent, which did not author `SpectralTracePassage.lean`.
No edits or compiler processes were performed by the reviewer. The pinned
referee standards have SHA-256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.
The prior `SPECTRAL_TRACE_PASSAGE_STATEMENTS.md` has SHA-256
`36305bf740f3eede2a979ab3bcd5fd2a77974acb4822e5788dabbef1b320261c`.

## Exact mathematical scope

This module proves equation (31) under two explicit premises: the fixed-index
limits for every original j≥1, and the eventual reciprocal majorant for
j≥2. It does not assume a trace limit. The first premise is intended to be
derived from the hypothetical critical UniformBound; the second must be
discharged by actual interlacing. Its conditional status is mathematically
necessary and is accurately stated in the source and lock.

- `inverseSpectralTerm` at line 18 has zero-based counting index k and
  the original one-based eigenvalue index k+1. The guard `k<n` retains
  every original index 1 through n, with no added j=0 or omitted j=n.
  At n=0 every term is zero. Lines 23–29 prove nonnegativity from actual
  strict spectral enclosure for each term that survives the guard.
- `tsum_inverseSpectralTerm_eq_trace` at line 32 proves finite support,
  converts the range sum to Fin n, and invokes the actual one-based
  reciprocal trace identity. The factor is exactly `h^(2*m)` with
  `h=1/(n+2)`, which is the normalization of the actual rational trace
  limit used in the final contradiction.
- The inversion proof at line 59 uses a strictly positive fixed-index
  limit: pi is positive and `k+1+(m-1)/2>0`. It does not invert a zero
  limit. The guard is eventually true for every fixed k. Natural-to-real
  casts give exactly `k+1+(m-1)/2`, and inversion gives both inverse
  powers, with no missing pi or shift factor.
- The main passage at line 90 does not apply the j≥2 estimate to j=1.
  Lines 107–114 use convergence of the actual first term to bound its
  norm eventually by `D=norm(L)+1`. The dominating sequence at line 115
  adds a single mass at k=0 to `C/(k+1)^(2*m)`. It is summable for m≥1
  by the previously proved even-zeta HasSum and a finite singleton sum.
- Lines 120–139 establish one eventual n threshold that works for every
  k. The first term uses D, each surviving k>0 uses the exact j=k+1≥2
  majorant, and the remaining terms vanish. Positivity converts the
  latter spectral upper bound into the norm bound that Tannery requires.
  Thus there is no illicit exchange of a pointwise threshold and a
  uniform threshold.
- Lines 140–142 use the proved counting-measure dominated-convergence
  theorem and the exact finite-trace identity. The resulting series and
  prefactor are precisely the ones in `trace_series_irrational`; no
  assumed series evaluation or assumed contradictory limit enters.

No material issue was found. The separate dependency `InverseSpectralTrace`
is source SHA-256
`4cd1c1189a56438237db1f217bc6c3172032f955ff5d030f86cd7f4fd1129b1d`;
its standalone proof review is assigned to the other referee. This report
reviews its exact use here, not the whole inverse-matrix import chain.
The unchanged manuscript has SHA-256
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`.

## Independently checked local evidence

The reviewer recomputed and matched every source/log/output hash against the
coordinator's actual execution record, which reports exit code 0, unchanged
source, `LEAN_NUM_THREADS=1`, and
`lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/SpectralTracePassage.olean MF21Restart/SpectralTracePassage.lean`.

| Artifact | SHA-256 |
| --- | --- |
| `MF21Restart/SpectralTracePassage.lean` | `4366c06110bbd59395afb9993704f8dac810bf573921a37aa8624e79ebff5610` |
| `evidence/logs/spectral-trace-passage-02.json` | `c2bb0ff1c35aba8fd464b56979baa579b7a969afa275d53a8d5190e6657c0447` |
| `evidence/logs/spectral-trace-passage-02.log` | `58c52e5684f168b05fe7cef0b459449394012e77ef90c9a818f92de9be0160f8` |
| `.lake/build/lib/lean/MF21Restart/SpectralTracePassage.olean` | `6de19a4326937ba2a3b6025c219dcd3c63eae0739d87fb2d6a42093988095b7e` |

All four public axiom reports use only `propext`, `Classical.choice`, and
`Quot.sound`. The warnings concern an unused hm in the generic inversion
helper and two unused simplifier arguments; they do not change the stated
limits or assumptions. The eight-module project import closure has no
proof-side `sorry`, `admit`, custom `axiom`, `native_decide`, or `unsafe`
marker and does not import Challenge. This is actual local Lean evidence,
not Comparator or GitHub verification, and it does not by itself complete
the original three-part Target.
