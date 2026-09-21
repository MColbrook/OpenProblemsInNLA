# External transcendence proof: locally checked port

The six files under `LeanFormalizations/NumberTheory/Transcendence/` were
copied from [gotrevor/lean-formalizations](https://github.com/gotrevor/lean-formalizations/tree/3a24a73416f83c32b4d4a2ac09588524c6291650)
at commit `3a24a73416f83c32b4d4a2ac09588524c6291650`.
Original authorship is retained; they are not a contribution of this MF-21
formalization. The upstream Apache-2.0 license is in `LICENSE` and exact
source hashes and URLs are in `upstream-manifest.json`.

These files were originally written for Lean/Mathlib 4.31.0. All six now
compile serially in this project's pinned 4.33.1 environment with one thread
and 4096 MiB. The actual integrated run is
`evidence/runs/20260920T192436920920Z/record.json`; its π theorem axiom
report contains only `propext`, `Classical.choice`, and `Quot.sound`.
This is a local Lean run, not a GitHub Comparator or independent kernel run.

Four source files are byte-identical to upstream. Two replace broad Mathlib
imports with sufficient narrower imports to fit the memory limit; one also
supplies an explicit `powersetCard_zero_right` simplification required by
the newer library. Exact changes are in `port.patch`, with original and
ported hashes recorded separately. Two independent reviews inspect the
source comparison and the proof/axiom scope under `reviews/`.

The exact checked conclusion is
`LeanFormalizations.Transcendence.transcendental_pi_axiomClean :
Transcendental ℚ Real.pi`. No axiom substituting for this conclusion is
permitted. No new claim about MF-21 follows merely from compiling it.
