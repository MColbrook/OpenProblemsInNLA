# Independent review: the actual critical-bound fixed-index limit

Verdict: **APPROVE** for the fixed-Y implication (30). Reviewed on
20 September 2026 by the Lean-audit agent, which did not author
`ActualFixedIndex.lean`. No edits or compiler processes were performed by
the reviewer. The pinned referee standards have SHA-256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.
The prior `ACTUAL_FIXED_INDEX_STATEMENTS.md` lock has SHA-256
`d10a4406d1b3f5839cd31430330a98be45a815d22789734a8cf7d3357f1a6985`.

`critical_bound_implies_actual_fixed_index_limit` at source line 18 uses
the actual implicit phase Y, its uniform equation and displacement estimate,
the full Taylor sum through order `2*m`, and the hypothetical original
`UniformBound m (implicitPhaseCoefficient m Y) (2*m)`. Its conclusion
is the exact limit `pi^(2*m)*(j+(m-1)/2)^(2*m)` for every original j≥1.
The coefficient family and one-based indexing are unchanged.

The proof does not apply a tail-only eigenangle theorem to small indices.
Lines 43–49 first put each fixed mesh point in the genuine IFT rectangle
eventually, using n≥j and h≤ε/2. Lines 50–67 prove Y tends to zero from
`|Y-mesh|≤C*h` and `mesh=j*pi*h`. The bound's constant may depend on the
fixed j, which is appropriate for a fixed-index limit. No spectral
approximation at j≥J is used here.

Lines 68–75 retain the literal equation `y=pi*j*h+h*eta(y)` with the correct
sign. Lines 76–86 specialize the order-`2*m` Taylor formula at the same
mesh and normalize its error to `B/(n+2)^(2*m+1)`. The expansion includes
the k=`2*m` term. It therefore cancels the same complete sum in the
hypothetical critical UniformBound; no endpoint coefficient is omitted
or separately assumed to vanish.

Line 89 applies the previously checked `FixedIndex` result to the actual
sequence with all former analytic premises now derived. In that dependency,
`FixedIndex.lean:100`, the critical UniformBound is consumed to obtain an
error of order `h^(2*m+1)`, so the conclusion does not follow from
contradictory or unused limit premises. The current dependency SHA-256 is
`da98fb1baae1b4b1736f5be8f03261b4a609182342df6158ac2394713313fc28`.
Finally, lines 90–95 substitute the proved endpoint value of eta and use
`m≥1` to interpret the natural subtraction `m-1` correctly. The pi factor
and the half-integer shift match manuscript (30).

No material issue was found. The explicit positivity premise for C is
redundant for this fixed-limit argument, as the compiler warning notes;
it is consistent with the actual IFT data and creates no vacuity. This
component remains an implication under the hypothetical critical bound,
not an unconditional conflicting spectral limit. It does not itself
assert the dominated trace passage or the complete original Target.

The reviewer recomputed and matched the following hashes against the
coordinator's actual local execution record. The record reports exit 0,
unchanged source, `LEAN_NUM_THREADS=1`, and
`lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/ActualFixedIndex.olean MF21Restart/ActualFixedIndex.lean`.

| Artifact | SHA-256 |
| --- | --- |
| `MF21Restart/ActualFixedIndex.lean` | `675e4abb114e5ebe8f824d7749096f520b315542303e634db1eb452c99a0b0be` |
| `evidence/logs/actual-fixed-index-02.json` | `5df35db99961c0677dd09186765f9060e4d8fd792234663ebb147006045faa5d` |
| `evidence/logs/actual-fixed-index-02.log` | `bec3e205526d20bd8cabae755ab332cf0cab3ceac68497ebc304c1ab7952b85e` |
| `.lake/build/lib/lean/MF21Restart/ActualFixedIndex.olean` | `98909f4bd541cf2ca84686326267504ae7bf36418612dfef16ed70364621f50d` |

The one public axiom report uses exactly `propext`, `Classical.choice`,
and `Quot.sound`. The 19-module project import closure has no proof-side
`sorry`, `admit`, custom `axiom`, `native_decide`, or `unsafe` marker and
does not import Challenge. The frozen manuscript remains SHA-256
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`.
No Comparator or GitHub final verification is asserted.
