# Independent review: the actual implicit-grid spectral error

Verdict: **APPROVE**, for the scope specified here. Reviewed on 20 September
2026 by the Lean-audit agent, which did not author `SymbolDerivative.lean`,
`ImplicitSpectralError.lean`, or `ImplicitSpectralData.lean`. No source edits
or compiler processes were performed by the reviewer.

The pinned referee standards have SHA-256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.
The prior `IMPLICIT_SPECTRAL_ERROR_STATEMENTS.md` lock has SHA-256
`c09d8460a63920a1d263c89900bad65610a875da503b05861eb5b406b46e2608`.
The unchanged original manuscript has SHA-256
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`.

## Scope and independence

This review covers the actual derivative bound, identification of the exact
phase preimage with the existing implicit function, the literal error (25),
and retention of the same coefficient family. It does not independently
re-review `PhaseQuantitative.lean`: that dependency was authored by this
reviewer. Its source is still
`bc649144eeafa74c1f0435e4bb90df7a679780c22cb709f2525b9c32be4b9649`,
and its separate referee-B review is
`reviews/phase-quantitative-referee-b.md`, SHA-256
`da3dc7026f4931c0654e4d476c4f44f867d4f6f9a9d82eecfd097236fea2a46b`.
The derivative and gluing arguments newly reviewed here are distinct from
that earlier actual phase-location proof.

## Source fidelity and mathematical audit

- `SymbolDerivative.lean:18` differentiates the literal symbol
  `(2*sin(t/2))^(2*m)`. The derivative is
  `(2*m)*(2*sin(t/2))^(2*m-1)*cos(t/2)` with natural subtraction in
  the exponent. The inner derivative's factors 2 and 1/2 cancel; no
  missing factor remains. At `m=0`, the outer factor is zero and the
  symbol is constant, so the total statement is still correct.
- Lines 26–41 derive the bound for every `t≥0` using the actual sine and
  cosine bounds. Lines 44–56 apply the convex-interval mean-value theorem
  to two points in `[0,T]`. The hypotheses ensure the entire segment is
  nonnegative and bounded by T; no derivative bound or differentiability
  premise is left to the caller.
- `ImplicitSpectralError.lean:19` proves identification with Y by the
  already constructed interval uniqueness property. Lines 28–38 check
  the exact point `(j*pi/(n+2),1/(n+2))` lies in the enlarged rectangle.
  Lines 39–49 prove, from the literal phase equation,
  `y=mesh+h*manuscriptEta m y`, with the correct positive sign. The
  positive denominator `n+2` is proved; there is no limiting or
  approximate phase equation. The given y lies in the larger uniqueness
  interval even at the endpoints 0 and pi.
- The helper's explicit `hε>0` is redundant once its positive step is
  smaller than ε, as the compiler's harmless unused-variable warning
  records. It is consistent with the existing shared interface and is
  not an impossible or restrictive extra assumption. More importantly,
  all uniqueness assumptions are discharged in the actual existence
  theorem; they do not remain as premises of an MF-21 claim.
- `ImplicitSpectralError.lean:53` keeps `N,J,C,c` before n and j and
  requires `n≥N`, `J≤j≤n`, with `J≥1`. It uses the original one-based
  eigenvalue and the proved actual phase preimage. It does **not** assert
  a global exponential bound down to j=1. Its additional n threshold
  makes `1/(n+2)<ε` uniformly (lines 73 and 79–90), without choosing a
  different Y for each n.
- Lines 98–116 apply the derivative estimate on
  `[0,A*j/(n+2)]`, containing both actual angles. The derivative supplies
  `h^(2*m-1)*j^(2*m-1)` and the angle displacement supplies
  `h*exp(-c*j)`. The proved exponent identity is used explicitly. The
  constant `B=(2*m)*A^(2*m)` and final `C=max A B` correctly cover both
  the angle bounds and the resulting exact error
  `C*h^(2*m)*j^(2*m-1)*exp(-c*j)`. All factors used when enlarging the
  constant are proved nonnegative. This matches manuscript lines
  298–304, equation (25), including its index restriction.
- `ImplicitSpectralData.lean:17` retains the one actual Y obtained from
  the Taylor-and-vanishing theorem. The construction at lines 52–57
  returns identical r, ε, C, δ, Y, equation, uniqueness, coefficients,
  all-order remainder, and vanishing witnesses, then appends the newly
  proved spectral error using that Y's uniqueness proof. The coefficient
  family remains exactly `implicitPhaseCoefficient m Y k`. There is no
  order-dependent phase, alternate approximation family, or moved
  quantifier. In particular δ still precedes every Taylor order and the
  Taylor error at lines 32–36 is `Cp*|h|^(p+1)`, with **no** exponential
  factor inserted into that separate estimate.

No material issue was found. The actual same-Y result proves the bounded
ingredients (23)–(25) with their correct quantifiers. This review does not
claim low-index bounds, extension-independence of the coefficients, the
full UniformBound/BulkBound assembly, the trace obstruction, or completion
of the original target. The final existence wrapper is useful contract
preservation, not a separately counted original theorem.

## Source-matched local execution evidence

The reviewer independently recomputed each source, JSON-record, log, and
output hash below. All source/log/output hashes match the coordinator's
record. Each record reports exit code 0 and unchanged source, with
`LEAN_NUM_THREADS=1` and `lake env lean -j1 -M4096 -o <output> <source>`.

| Artifact | SHA-256 |
| --- | --- |
| `MF21Restart/SymbolDerivative.lean` | `ae15318c03af3eaa7060a50b9b47206450575cd934c8f93d420bc57e0b934519` |
| `evidence/logs/symbol-derivative-02.json` | `55c8bd8c554e22e1ac4aac936115e63473f69a702f5e6c1c61088f4183b25dbf` |
| `evidence/logs/symbol-derivative-02.log` | `34be3cfb177d24b9813bb910de7d07cc52aa67b6b1fea6a8e12c34a45c10913c` |
| `.lake/build/lib/lean/MF21Restart/SymbolDerivative.olean` | `9f2b4ad0f808a4ea9a7ea723175ae7e2a3ac4c37a5825eab8f409ff058b54d3d` |
| `MF21Restart/ImplicitSpectralError.lean` | `41da02350921c1a6e8cfae0c366ab1801e549c10d554752083f567705566cf2e` |
| `evidence/logs/implicit-spectral-error-01.json` | `1ee3948570aac82410142256f8d72f966a756a41a4c84c7fa21b55601eb03b8b` |
| `evidence/logs/implicit-spectral-error-01.log` | `5e6d52aa4cc7fa8fbd9c5fad2a664ffb547037d15bcacaae51ddfb88e13c9f87` |
| `.lake/build/lib/lean/MF21Restart/ImplicitSpectralError.olean` | `f68955bc58a3bf64f7479ff1a631bd12eda9e78bd1449e90b411217f57d9fbd4` |
| `MF21Restart/ImplicitSpectralData.lean` | `e379ad2cfd444ba82aa0f10e9c4d51c2bf61d081836754c24ae7c2029fd1bc1b` |
| `evidence/logs/implicit-spectral-data-01.json` | `dde63d27bcc87cc623d92566043492ecb61a76e1cb1696065bc5e4399899088e` |
| `evidence/logs/implicit-spectral-data-01.log` | `9dc105bf979408e2455aee20f606c36cd5444000624c6df9cf0dec8b0a595c97` |
| `.lake/build/lib/lean/MF21Restart/ImplicitSpectralData.olean` | `fca381cae4798271271a53e22693954638fd5edb011c257945f69963fc3d6b3e` |

The logs contain respectively 3, 2, and 1 public theorem axiom reports,
all exactly `propext`, `Classical.choice`, and `Quot.sound`. The only
warnings are two tactic-sequencing style warnings in the derivative proof
and the redundant `hε` noted above. Textual scans of the project import
closures (2, 68, and 69 modules) found no proof-side `sorry`, `admit`, custom
`axiom`, `native_decide`, or `unsafe` marker and no Challenge import.
These are local Lean checks. Comparator and GitHub final verification are
not asserted or inferred from this evidence.
