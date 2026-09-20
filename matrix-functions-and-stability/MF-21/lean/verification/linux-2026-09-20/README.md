# Actual MF-21 Linux verification — 20 September 2026

**Accepted.** The repository's unchanged `tools/lean/verify.sh` verified all
five selected MF-21 contracts from local commit
`e378ec4679f9119aacf79a0fe30b80493a61ec5b`. The command exited zero after
printing `Lean default kernel accepts the solution` and `Your solution is okay!`.

This was an actual non-root Ubuntu 24.04 ARM Linux run in an isolated local
Tart VM, with a working user systemd session, Landrun and Bubblewrap. The
pinned sandbox and kernel/Comparator negative controls ran unchanged. No
shared host directory or substitute sandbox was used. Dependency preparation
downloaded public pinned sources and the Mathlib cache; the proof build and
export ran under the prescribed network restriction. This was not a GitHub
Actions run, and no code was pushed or uploaded to GitHub.

## Checked scope

- `NLA.MF21.full_target`: all three original assertions for every `m ≥ 3`.
- `NLA.MF21.universal_obstruction`: no continuous family attains the forbidden
  uniform next order.
- `NLA.MF21.smooth_common_family`: one smooth family satisfies all estimates
  and the matching finite-head lower/global upper error bounds.
- `NLA.MF21.fourier_matrix_entries`: the actual signed-binomial matrix equals
  the source's Fourier-integral matrix entry by entry.
- `NLA.MF21.coefficients_unique`: equality of continuous bulk coefficient
  families on the entire closed interval.

The specification has no replaceable definition holes. Comparator enforces
the transitive axiom allowlist `propext`, `Classical.choice`, `Quot.sound`.
The default kernel accepts the exported solution against the independently
specified theorem contracts. The separate fresh macOS replay additionally
audited all 1,354 local declarations, including unexported/generated ones.

## Retained evidence

- [Machine receipt](result.json): exact commit, 96 input hashes, tool receipt
  and contract configuration.
- [Complete Comparator log](comparator.log), [selected contract output](selected-contract-output.log)
  and [actual printed axiom reports](actual-axioms.log).
- [Sandbox controls](sandbox.log), [kernel controls](kernel-controls.log),
  [Comparator controls](comparator-controls.log), [sorry rejection](negative-sorry.log)
  and [native trust rejection](negative-native.log).
- [Immutable checked input snapshot](trusted-inputs.tar.gz) and
  [input manifest](trusted-input-manifest.json).
- [Complete execution log archive](full-logs.tar.gz),
  [bootstrap/tool receipt](bootstrap.json), and
  [capture-time consistency summary](evidence-summary.json).

SHA-256 values:

```text
result.json
aaedb2d6a7c9e30e34ce4f0b2696b54dcafd7329b0ed8ad80ed7fcfd5b6da168
full-logs.tar.gz
94988ded35ef4ac20f877632b80c130582574a88e217d7158f9834bd9ddbb6e6
trusted-inputs.tar.gz
360046e0ca4cb5bc60cce8c60f8d9b129934c3884c661c10f794d397077cf136
```

The coordinator independently matched all 96 inputs, the exact five-contract
configuration, the kernel-acceptance marker, exit status and all 251 printed
axiom reports against the current files at evidence capture. The separate
[nonauthor proof/runtime review](../../reviews/independent-proof.md) records
its own inspection. Mathematical source correspondence is also reviewed
in the [independent fidelity report](../../reviews/independent-fidelity.md).
These are AI-agent reviews; no human peer-review or source-author endorsement
is claimed.

## Later publication files

The checked snapshot deliberately retains the then-pending status text in
its README and metadata. After acceptance, those two documentation files were
updated, and review/evidence files and manuscript renderings were added. All
Lean sources, Challenge, Comparator configuration, Lake files and toolchain
remain byte-identical to the accepted proof revision. The final
`publication-input-comparison.json` records this distinction. No claim is
made that later editorial text itself was an input to the earlier execution.

Reproduction uses the committed snapshot and the repository's
[`HARNESS.md`](../../../../../tools/lean/HARNESS.md). Existing receipts do not
replace a fresh check after any mathematical or build-input change.
