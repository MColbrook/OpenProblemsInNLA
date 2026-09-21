# Independent review: the actual coefficient vanishing bounds

Verdict: **APPROVE**, for the bounded scope below. Reviewed on 20 September
2026 by the Lean-audit agent, which did not author either reviewed source.
No source edits or Lean/compiler processes were performed by this reviewer.

The review applies the pinned referee standards, SHA-256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`,
to `VerticalPowerFactor.lean`, `CoefficientVanishing.lean`, and their prior
`COEFFICIENT_VANISHING_STATEMENTS.md` lock. The latter has SHA-256
`d31029ee70a3a46ac319392075c300faaf21aebbdc2eb64a6103c6b1c33ac48b`.
The frozen manuscript remains SHA-256
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`.

## Statement and proof fidelity

- Manuscript lines 289–296, equation (24), require the actual family
  defined by the derivatives in (5), with bounds through order `2*m`.
  `CoefficientVanishing.lean:20` states exactly
  `|implicitPhaseCoefficient m Y k x| ≤ Ck*x^(2*m-k)` for every `k≤2*m`
  and every `x∈[0,π]`. Each positive `Ck` is independent of `x`; the
  phase `Y`, its neighborhood, and its coefficient family are fixed
  before `k`. No free coefficient array or assumed vanishing estimate
  substitutes for that definition.
- `VerticalPowerFactor.lean:15` explicitly defines the residual factors.
  The proof at line 34 obtains the exact power factor by induction and
  differentiation. The neighborhood equality at lines 43–51 is necessary
  and present: it is an equality on an actual neighborhood, not a
  pointwise identity being differentiated. The successor bound supplies
  `N-k≥1`, making the natural-subtraction exponent identities at lines
  65–66 valid. The proof uses only product and power rules and performs
  no division by `u`.
- The use of `ContDiffAt ℝ ⊤` is consistent with the pinned library's
  analytic order `ω`. In particular, passing to an analytic neighborhood
  at line 46 is justified by the actual regularity hypothesis. The
  scoped transparency option at line 31 changes elaboration, not the
  proposition or trusted axioms.
- `CoefficientVanishing.lean:28` uses the literal
  `u(x,h)=2*sin(Y(x,h)/2)` and exponent `2*m`. Lines 50–58 unfold the
  original derivative/factorial coefficient and apply the proved
  identity. Compactness bounds the continuous remaining factor on
  `[0,π]` at lines 38–47. The exact initial value `Y(x,0)=x` and
  `|sin t|≤|t|` give `|u(x,0)|≤x` at lines 59–67. Factorial positivity,
  multiplication, and the power inequality finish the estimate.
- Endpoints are literal. At `x=0` and `k<2*m` the positive exponent
  forces the coefficient to vanish. At `k=2*m` the exponent is zero,
  including at `x=0`, so the theorem asserts a bound rather than a false
  zero. `k=0` and `x=π` are included. The generic helper even permits
  `m=0`, when only `k=0` is admitted; no contradictory positivity
  assumption is used to make it vacuous.
- The actual theorem at `CoefficientVanishing.lean:83` obtains the one
  constructed `Y` from `manuscript_uniform_implicit_taylor` and returns
  the same witnesses at lines 106–110. All prior equation, uniqueness,
  coefficient analyticity, `d₀=g`, and Taylor conclusions are retained.
  The common positive `δ` precedes every Taylor order `p`, and the
  remainder remains `Cp*|h|^(p+1)`. The final vanishing assertion uses
  that same family. The generic initial-value hypothesis is discharged
  on the closed interval at lines 111–114; it is not left as a premise
  in the actual theorem.

No material issue was found. This review establishes fidelity for the
coefficient estimate (24) and its combination with the existing same-family
Taylor theorem. It does not claim an independent re-review of every imported
proof, an eigenvalue error estimate, extension-independence of the family,
the low-index estimates, or the complete MF-21 target.

## Independently checked local evidence

The reviewer recomputed all source, log, and output hashes below and matched
them against the actual coordinator execution records. Both records report
exit code 0, `source_unchanged: true`, `LEAN_NUM_THREADS=1`, and the command
`lake env lean -j1 -M4096 -o <output> <source>` in this project. No test was
rerun by the reviewer.

| Artifact | SHA-256 |
| --- | --- |
| `MF21Restart/VerticalPowerFactor.lean` | `a0e81d664704689e4675d6bcaf96f47bf4be1fd6bdb0f6addfc797fb528d01d2` |
| `evidence/logs/vertical-power-factor-01.json` | `20b295cf9c0fdf8b90cd732dde978c82ed13a05e93c4918074a29a1b6a8c22d9` |
| `evidence/logs/vertical-power-factor-01.log` | `d230c63e2fb9c8b0121b023df35effbe953a5ef626b13e2c0125222d12011e9e` |
| `.lake/build/lib/lean/MF21Restart/VerticalPowerFactor.olean` | `e7666e1843b223694ee034371825ef6d6e4e3e8d2e592c6883ac00135fda4f68` |
| `MF21Restart/CoefficientVanishing.lean` | `2444222b2fd0560e420a477ccfad6bc87cc7a7f3a9c4a24ce3855f27a82327ff` |
| `evidence/logs/coefficient-vanishing-02.json` | `08589909276940c79ed8a70d0e5dbbc91728fb58c63cc2253110078322652e1e` |
| `evidence/logs/coefficient-vanishing-02.log` | `4bc0380f7155c69dee8c6d478826d2d40b09940c49cd3f4de4d399dcef70de21` |
| `.lake/build/lib/lean/MF21Restart/CoefficientVanishing.olean` | `2a5800980526e20f64cd247f8f354cbc6953ae4babaf967974860d537229ffe7` |

Each log contains two public theorem reports, all using exactly the standard
axioms `propext`, `Classical.choice`, and `Quot.sound`. A textual scan of the
project import closures (2 and 17 modules respectively) found no proof-side
`sorry`, `admit`, custom `axiom`, `native_decide`, or `unsafe` marker.
No Challenge placeholder is imported through either closure. These are actual
local Lean results. No Comparator or GitHub final verification is asserted.
