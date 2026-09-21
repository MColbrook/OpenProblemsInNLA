# Independent source review: sublists through the upper endpoint

Verdict: **APPROVE** for the four mathematical statements and proofs in
`MF21Restart/CharacteristicSublist.lean` at SHA256
`29ec8cd3beec7b1ec5b60a8788961fc755f1620975a35dfead59cce82acb8448`.
I found no material source-fidelity, correctness, or hypothesis issue.
The observed successful CharacteristicSublist01 JSON, log, and current output
all match this exact source. Local execution was by the coordinator; this
reviewer ran no compiler.

I read the actual source, its statement lock, the root norm/distinctness
proofs, and the imported slope-based normalized Vandermonde definitions and
exact factorization. This applies the pinned referee rubric, SHA256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.
No reviewed source was edited and no compiler was run by this reviewer.

`characteristicRoots_eq_implies_index_eq_or_oscillatory` first separates
stable, unit, and exterior roots by their strict norm regions. Within the
stable and exterior regions it uses the proved actual stable-root
injectivity, valid on `0<theta≤π`. Cancellation of reciprocals preserves
the exterior equality. The only remaining indices are m-1 and m. The
conclusion correctly permits either ordering of that pair, while permitting
equal indices in every region. It does not assert that the pair actually
coincides below π, nor full-list injectivity at π. Zero is necessarily
excluded because all roots coincide there.

`characteristicRoots_sublist_injective` assumes an injective index map
u and the explicit condition that its image does not contain both central
indices. The condition quantifies over every i,j, so it rules out both
orientations of the exceptional pair; the proof explicitly swaps i,j in
the reversed case. It is an index-separation condition, not a hidden
assumption of distinct actual root values. Its conclusion is exactly the
needed actual sublist injectivity through π.

`normalizedRootVandermonde_ne_zero_on_Icc` handles zero by the proved
distinct tangents of the actual roots. Away from zero, it applies the
actual Vandermonde determinant criterion to the just-proved sublist
injectivity and rewrites the exact identity
`V(roots)=theta^degree*normalizedV`. A nonzero product has a nonzero
normalized factor. This use of factorization does not divide at zero
or assume an order of vanishing. The imported normalized Vandermonde is
the determinant of the individual derivative-completed root slopes,
whose differences have the correct later-minus-earlier orientation.

`normalizedBoundaryCoefficient_ne_zero_on_Icc` assumes a cardinal-m
subset separating the two oscillatory positions. Its membership condition
is exactly that one central index lies in the subset and the other in
the complement. Hence neither inherited-order sublist contains both.
Both order embeddings are injective, and the preceding theorem makes
both normalized Vandermonde factors nonzero. The actual Laplace sign
is a unit ±1 and remains nonzero after its integer-to-complex cast.
Their product is the existing `normalizedBoundaryCoefficient`; no
alternative coefficient is substituted.

The separation condition is necessary for a statement including π:
at m=2, the subset consisting of the two oscillatory indices has a zero
Vandermonde factor at π and does not satisfy that condition. In contrast,
each leading subset in manuscript (15) puts one unit index in each part
and will satisfy it once its set facts are supplied. The theorem is
therefore nonvacuous and its hypothesis reflects the actual denominator
structure, rather than replacing a nonvanishing conclusion by an assumed
root-separation estimate.

The statement allows k=0 and k=1 in the sublist lemmas; the corresponding
Vandermonde determinants are one. It uses m≥2, covering the original
m≥3 domain. At theta=0 the normalized values are nonzero, while the raw
root Vandermondes may vanish; at theta=π only the central collision has
to be excluded. These distinctions agree with the paragraph following
manuscript (18), line 211.

No custom axiom, `sorry`, `admit`, unsafe shortcut, `native_decide`, or
numerical oracle occurs. I found no inappropriate strengthening or
unproved regularity premise. This module supplies nonvanishing of the
appropriate normalized denominator factors on `[0,π]`. It does not by
itself identify the leading subsets, prove their signs or equation (15),
bound the normalized coefficient ratios, construct the real determinant
remainder, or verify the MF-21 target. No original-problem completion is
counted.

I read the retained CharacteristicSublist01 JSON and log and recomputed the
current source, log, and `.olean` hashes. They match the record, which reports
source unchanged and exit 0 for `lake env lean -j1 -M4096 -o
.lake/build/lib/lean/MF21Restart/CharacteristicSublist.olean
MF21Restart/CharacteristicSublist.lean`. All four printed declarations use
only `[propext, Classical.choice, Quot.sound]`. This is actual local evidence
from the coordinator, not a compiler execution by this reviewer or a GitHub
Comparator check. No GitHub workflow or Comparator result is claimed.

| File | SHA256 |
|---|---|
| `MF21Restart/CharacteristicSublist.lean` | `29ec8cd3beec7b1ec5b60a8788961fc755f1620975a35dfead59cce82acb8448` |
| `CHARACTERISTIC_SUBLIST_STATEMENTS.md` | `bb1b324365a571ffd4f61d21453067b6e25f5a098ae4a36ccff0718e5f76199e` |
| `MF21Restart/NormalizedBoundary.lean` | `3d45a02be0ce050f37be4ec3db227504028730c9283f4148d5739b37c48a9261` |
| `NORMALIZED_BOUNDARY_STATEMENTS.md` | `17bbca3cecdc1088d1dfa0f8d4bed5cde78d28d6bdd93c39b2961ba2b494fc28` |
| `evidence/logs/characteristic-sublist-01.json` | `38dbc962ccbe3b2048e8766eff6688bc0d9d3afa5f2aea39b269a5ef2b8c8c51` |
| `evidence/logs/characteristic-sublist-01.log` | `4a98cee186656389471b4ae7b27d1df40c3357b71e03221fcf638d6495c42588` |
| `.lake/build/lib/lean/MF21Restart/CharacteristicSublist.olean` | `fa65787b6aa29615a7d10bbd5d48b9bb79938fc6207bad0933db6842619fe8db` |
