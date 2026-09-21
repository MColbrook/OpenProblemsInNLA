# Independent review: OrderedTailCounting

Verdict: **APPROVE** for the one declared finite counting theorem.
Reviewer: `/root/mf21_restart_manuscript`, independently of its author
`/root/mf21_restart_lean_audit`. Review completed 20 September 2026.

I read the exact statement lock, complete proof source, and retained
local test record/log. I ran no Lean compiler. This report applies the
pinned `REFEREE_STANDARDS.md` rubric (SHA256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`).

## Exact reviewed artifacts

| Artifact | SHA256 |
| --- | --- |
| `MF21Restart/OrderedTailCounting.lean` | `d00ea3122874cd22ec71f71fe05b0f66371aef2e2f5902c4976ecd0fea22d9af` |
| `ORDERED_TAIL_COUNTING_STATEMENTS.md` | `7e678d9f100bb0855b9e5c27b92ae315cd24f97bef09ec13ce57890fcdcf2c60` |
| `evidence/logs/ordered-tail-counting-01.json` | `c63be06c95505d686bfc20be4eb6b71b2d0e140a56bd8030e31abfc592e3f580` |
| `evidence/logs/ordered-tail-counting-01.log` | `eeb93a47c092d290d0cac13c0778590018b06729c0e6133480e06444bc6df194` |
| `.lake/build/lib/lean/MF21Restart/OrderedTailCounting.olean` | `3b2436050e5c915f1a777068c764c1acf806915e285b490ff5b07fb4ca23b183` |

I recomputed these hashes. The source, log, and output hashes match the
JSON record. It records `LEAN_NUM_THREADS=1` and the actual local command
`lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/OrderedTailCounting.olean MF21Restart/OrderedTailCounting.lean`,
exit code 0, and unchanged source. The log reports exactly
`propext`, `Classical.choice`, and `Quot.sound` for
`MF21Restart.ordered_tail_index`. No GitHub Comparator result is claimed.

## Statement fidelity and proof

The theorem has exactly the locked quantifiers and concludes the literal
one-based-label/zero-based-position equality `a (k-1)=b k`. It does not
assume that equality, strict ordering of the whole array, or simplicity
of values below the tail. The tail starts at `J>=1`, ends at the actual
array length n, and every labelled tail value has exactly one array
occurrence. Coverage is required for **every array position** with value
at least `b J`, including repeated positions if present. This is the
right multiplicity-sensitive premise for the manuscript's top-down
counting argument.

The proof fixes k and its unique position p, then uses `Finset.card_bij`
between labels `Icc k n` and positions `Ici p`. Monotonicity of a and
strict ordering of b place the selected occurrence of each label above
p; if a candidate lies below p, ordering forces the same label and
uniqueness forces the same position, a contradiction. Strict ordering
also gives injectivity. Conversely any position at or above p has value
at least `b k`, hence at least `b J`; coverage supplies its label and
strict ordering makes that label at least k. Unique occurrence gives
surjectivity. Thus `n+1-k=n-p.val`, and the available natural bounds
justify `p.val=k-1` without truncated-subtraction ambiguity.

The endpoint cases `J=n`, `k=J`, and `k=n` are included. The hypotheses
exclude n=0, as required to have a nonempty positive-labelled tail. Low
values may repeat arbitrarily. No condition is unused in a way that
hides the desired result, and no impossible auxiliary assumption is
introduced. The proof reuses finite interval/cardinality APIs and has
no numerical computation, custom axiom, `sorry`, or `admit`.

## Scope limitation

This is an abstract ordered-array lemma. Actual eigenvalue monotonicity,
strict ordering of the phase-root values, unique spectral occurrence,
and upper-tail coverage must still be supplied by the concrete MF-21
application. This report does not claim that original eigenvalue indices
have already been identified, does not review any later application,
and does not certify the full unchanged target or Comparator contract.
