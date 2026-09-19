# MF-14: formalization of the original negative answer

Formalization by **George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology**, with substantial AI assistance. The degree-44 mathematical construction is due to **Marcus Webb, University of Manchester**. The earlier degree-42 result remains attributed to **Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge**. Prior library and source authorship is retained.

The formalized conclusions are `NLA.MF14Degree44.degree44_coverage : NLA.MF14.CoversDegree 44` and `NLA.MF14Degree44.original_equality_false : ¬ IsGreatest NLA.MF14.coveredDegrees 42`. They refute the unchanged original question. The model uses complex scalars, at most seven chronological products, and the full 129-dimensional coefficient ambient space. The simultaneous four-output prefix and its common circuit are retained through the closure argument.

The repository's later mathematical resolution `d₇ = 47` remains documented in its existing sources; that stronger equality is **not formalized by this degree-44 project**. This is one existing original target, with no new mathematical resolution counted. The separate degree-47 work and evidence remain preserved.

## Current verification scope

Root's actual local runs `recovery-086` and `recovery-087` passed the full final theorem and the aggregate audits of all 25 frozen contracts. They used one Lean compiler, one thread, and a 4096 MiB memory cap. The final review snapshot is `e52fab5a7b58c3bc6fb2c2df1283d55c6e4352056689c900de936c12e2595436`. The aggregate source SHA256 is `e5c888faffd3a0936d55c7cb9ec59d24ea54a60b204f921d5ee68734f5124d44`. Every listed transitive axiom report contains only `propext`, `Classical.choice`, and `Quot.sound`.

Two wholly nonauthor final reviews **approved** the complete original-target proof: [referee A](reviews/final-referee-a/REPORT.md) and [referee B](reviews/final-referee-b/REPORT.md). Both audited the exact source bytes and existing local evidence; neither reran Lean or Comparator. The real GitHub Linux Comparator/kernel/sandbox checks are **pending**, so no completed-verification count is promoted by this draft. See `STATE.json`, `formalization.yaml`, and `PACKAGING-NEXT-STEPS.md` for the remaining gates.

## Proof and computation

The proof combines a simultaneous polynomial degeneration with the inverse function theorem and polynomial density. Exact first derivatives are connected to the actual maps, rather than accepted as stored tables. The 45-dimensional Jacobian is certified nonsingular using a checked inverse modulo 3. Natural-number residue computations are cast to the finite field after reduction. Sparse block determinants and coefficient identities avoid large symbolic expansions.

Pinned LeanCert supplies `#assert_trust kernel` audits. This degree-44 route uses exact modular and symbolic arithmetic; it requires no numerical interval evaluation. The previous degree-47 interval computation is not being reported as part of this proof. `NUMERICAL_TARGETS.md` is the preserved statement-first plan; its historical pre-proof wording does not replace the current verification record.

## Reproduction

From the `matrix-functions-and-stability/MF-14/lean` directory, run:

```sh
lake build Solution
```

The toolchain and dependencies are pinned in `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`. `Solution` is the sole default target. `Challenge` is isolated and is not imported by the implementation. Final Comparator execution uses the repository's pinned non-root Linux workflow; the eventual run URL and exact proof commit must be recorded before changing verification status.

The publication-name `Solution.lean` and isolated `Challenge.lean` also passed local run `recovery-088`. The [local audit](verification/local-2026-09-19/LOCAL-REPLAY-AUDIT.json) checks actual command logs and recursively authenticates successful source/dependency-matched reuse for all 86 proof modules. The archive script itself executes no Lean. A standalone local Lake build is not claimed.
