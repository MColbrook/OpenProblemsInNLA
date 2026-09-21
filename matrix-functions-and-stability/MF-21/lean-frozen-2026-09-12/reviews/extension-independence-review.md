# Independent review: smooth coefficients and extension independence

Verdict: **APPROVE** for the exact source versions below. No material mathematical, statement, or proof-trust issue found. Reviewer: `mf21_restart_lean_audit`, independently reviewing sources authored by the other agent. The reviewer ran no Lean compiler. This is source review plus independent inspection of the coordinator's retained local evidence, not a Comparator or independent kernel replay.

The review follows `REFEREE_STANDARDS.md`, SHA256 `e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`. The prior statement lock is `EXTENSION_INDEPENDENCE_STATEMENTS.md`, SHA256 `914bbc1ed61e6ad85902568e237552b519a4afa7a3bc8bf1d351c9a219aaf7d4`. The frozen manuscript remains SHA256 `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`.

## Exact scope and mathematical checks

- `SmoothCoefficient.lean:14` proves that every exact vertical iterated derivative of a jointly smooth real function remains jointly smooth. Lines 25–43 use the parametric Fréchet derivative and evaluation at 1, with the exact identity to the scalar iterated derivative. The regularity order is `∞`, not analytic order `⊤`. `parametricTaylorCoefficient_contDiffAt_infty` at line 45 restricts to `(x,0)` and divides by the constant factorial. It retains the derivative-defined coefficient rather than replacing it by an arbitrary family. The local elaborator option at line 13 changes typeclass unification behavior, not the proposition or kernel trust.
- `ExtensionIndependence.lean:23` quantifies over competing extensions agreeing with the actual symbol and eta on `[0,π]`, and a smooth competing implicit parametrization `Z`. Its hypotheses are the natural smoothness, zero-height, and implicit-equation properties. Equality of the coefficients or of the implicit functions is not assumed. Only agreement of the eta extension is needed once `Z` has been supplied; omitting a redundant eta-smoothness hypothesis does not weaken the conclusion.
- Lines 44–57 establish continuity in the horizontal parameter for both exact coefficient families. Lines 61–83 keep the competing solution inside `(0,π)` near `h=0` for each interior `x`, use the actual enlarged-interval uniqueness to identify its germ with `Y`, and then identify the composed symbol germs. Lines 84–87 pass to every iterated derivative and retain the same factorial normalization.
- Lines 88–90 extend coefficient equality to both endpoints by continuity and `closure (Ioo 0 π) = Icc 0 π`. The proof does not incorrectly assume that endpoint implicit solutions stay inside the original interval for both signs of `h`.
- The conclusion covers every natural derivative order for the same `Y`; it establishes the manuscript's extension independence after equation (5). It does not assert that different extensions agree outside `[0,π]` or that `Y` agrees away from zero height. This auxiliary result is separate from the three-part spectral Target. Existence of a competing parametrization is a hypothesis of this comparison lemma, while the project's actual `Y` was constructed in the separately reviewed implicit-phase chain.

## Exact local evidence

The reviewer recomputed the source, JSON record, log, and output hashes. Every source/log/output agrees with its retained record; both records have exit code 0 and `source_unchanged: true`. Both commands are `lake env lean -j1 -M4096 -o <recorded output> <source>`, with `LEAN_NUM_THREADS=1`.

| Item | SHA256 |
|---|---|
| `MF21Restart/SmoothCoefficient.lean` | `e6e21a777cb876fb84e63a32c679c066bdeaa0f64589444999cd190ffacb8dfc` |
| `evidence/logs/smooth-coefficient-02.json` | `12bf8ab56e1511a9eeac97ac628392652681eaf31f46efdfc55482a365edd863` |
| `evidence/logs/smooth-coefficient-02.log` | `de249a64860b580379d86d42d7867c9ac506296df5956c82eb1da268f4f440b5` |
| `SmoothCoefficient.olean` | `5ab4b61f54874a98cd287f5b59a7e5f1d6368a6c01158edfb8a65eef222fe6f4` |
| `MF21Restart/ExtensionIndependence.lean` | `bd4acdd599b5a263020c292231426399292f7e13a83cca076d88c9b01cc8f126` |
| `evidence/logs/extension-independence-03.json` | `26d4451ab846c9705e7f0d71093a46e0b229a2d8a1ce4556101f8b83e1b4faeb` |
| `evidence/logs/extension-independence-03.log` | `c6ec98ae571cb6b18d3ed1c1c712af7b2c94d0117be8b6f8f663580a069d42c3` |
| `ExtensionIndependence.olean` | `4404397f64c1f8d1512525bb2ef6d0fdaedc62867c914daa8b54cb83b398eed9` |

The two SmoothCoefficient reports and the one ExtensionIndependence report contain only `propext`, `Classical.choice`, and `Quot.sound`. A comment-stripped source scan of their respective 2-module and 17-module local import closures found no `sorry`, `admit`, custom `axiom`, `unsafe`, `native_decide`, `implemented_by`, or `extern`. Neither closure imports Challenge. The independently reviewed ParametricTaylor/ImplicitTaylor/implicit-phase dependencies are not reclassified as new proofs in this review. No Comparator run or completed-problem count is claimed.
