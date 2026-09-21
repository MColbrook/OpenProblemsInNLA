# Independent review: same-family global and bulk expansion assembly

Verdict: **APPROVE** for the stated component scope. Reviewed on 20 September
2026 by the Lean-audit agent, which did not author the three sources below.
No source edits or compiler processes were performed by the reviewer.
The pinned referee standards have SHA-256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.
The prior `EXPANSION_ASSEMBLY_STATEMENTS.md` has SHA-256
`3bb439782c9e88d72b91527f33e4758286a089ee93ca35489eb6002c9bc5543c`.

This review covers `ExpansionScalar.lean`, `ExpansionAssembly.lean`, and
`ImplicitExpansionBounds.lean`. It does not independently re-review the
reviewer's own `BulkDecay.lean` dependency, whose current SHA-256 is
`2d768009100ca3c3659739bc4c7de26999e1a866fb8b3c2b1d876ae50bdc7582`.
The actual Y/error construction has a separate independent report in
`reviews/implicit-spectral-error-review.md`. The original manuscript remains
SHA-256 `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`.

## Mathematical and statement checks

- `ExpansionScalar.lean:52` bounds `j^q*exp(-c*j)` for every natural j
  by composing the proved real limit with the natural inclusion and
  bounding the entire convergent sequence. This includes j=0 and q=0;
  no finite prefix is omitted. The positive constant is chosen before j.
- At line 65 the exact cutoff `ceil(log(n+2)^2)` eventually exceeds any
  fixed natural J. The proof explicitly makes the logarithm at least 1
  before comparing it with its square. There is no unproved monotonicity
  assumption on the squared logarithm near zero.
- The coefficient-sum estimate at line 86 uses one fixed family d and
  chooses each coefficient bound before n and j. For every summand,
  `k≤p≤2*m` justifies `2*m-k+k=2*m` at lines 126–132. Consequently the
  mesh power and the step power contribute exactly `h^(2*m)`.
  The nonnegative base `j*pi` is bounded by the fixed `J*pi`; no n-dependent
  constant is introduced. The cases J=0, j=0, and k=2*m obey ordinary
  natural-power conventions and do not invalidate the proof.
- `ExpansionAssembly.lean:15` proves every order p through `2*m-1`.
  Its finite-prefix spectral premise is explicitly at lines 29–31, not
  hidden in a coefficient hypothesis. The case j<J uses that bound and
  the actual coefficient-sum estimate. The complementary case j≥J uses
  the spectral comparison only in its proved range. Since `0<h≤1` and
  `p+1≤2*m`, the inequality `h^(2*m)≤h^(p+1)` has the correct direction.
  The Taylor remainder is separately of order `h^(p+1)` and has no
  exponential factor. All thresholds and constants precede n and j.
- `ExpansionAssembly.lean:103` proves the original `BulkBound` with the
  unchanged logarithmic-squared cutoff. It requires no finite-prefix
  eigenvalue bound. The cutoff is first made at least J, then the proved
  scale gain supplies `j^(2*m-1)*exp(-c*j)≤h`. This is exactly the extra
  factor of h required to turn (25) into order `h^(2*m+1)`. The full
  Taylor sum through `2*m` and the order-`2*m+1` Taylor remainder are used.
  The conclusion is the original denominator form of `BulkBound`.
- `ImplicitExpansionBounds.lean:16` exposes a fixed-Y interface so that
  later code can keep the original IFT data for the critical-bound
  contradiction. Its family is literally `implicitPhaseCoefficient m Y`.
  The theorem at line 45 selects one actual Y, derives the tail premise
  from its previously proved spectral result, and keeps the same family
  for continuity, d0=symbol, BulkBound, and all conditional global bounds.
  It does not select separate families for the two regimes.

No material issue was found. The unconditional bulk result and conditional
global assembly match manuscript Section 4, lines 280–308. The finite-prefix
premise is still a real obligation of these standalone statements; the
actual circulant proof must discharge it in final assembly. These modules
do not prove the critical obstruction or a complete original Target by
themselves, and wrappers are not additional completed targets.

## Independently checked actual local evidence

All hashes below were recomputed by the reviewer. Each execution record
reports exit code 0, unchanged source, `LEAN_NUM_THREADS=1`, and
`lake env lean -j1 -M4096 -o <output> <source>`; its source/log/output hashes
match the current files. No compilation was rerun by the reviewer.

| Artifact | SHA-256 |
| --- | --- |
| `MF21Restart/ExpansionScalar.lean` | `306f9b8ac8f987075cc9cd1beb53437eb541116cd42aa551cbc2bff15e0421b4` |
| `evidence/logs/expansion-scalar-02.json` | `fcceeeaef7d4ec87ebe37ac9a1de85114ce6c62889df8cb17feb85850c9fb229` |
| `evidence/logs/expansion-scalar-02.log` | `6b7008774f2e69f4b211bd82b80f7d31327f5d28f8f632da3a1ca6517562818f` |
| `.lake/build/lib/lean/MF21Restart/ExpansionScalar.olean` | `836cf419d9a3d7398afebbae907b5740eab641d2b947977833648242ff45c281` |
| `MF21Restart/ExpansionAssembly.lean` | `3a9fc651f39e373f88780653b6f95946292d667c3ae791ba861e337d471d431d` |
| `evidence/logs/expansion-assembly-02.json` | `f161fe29c1080a9a71f2c05955e13753249926e6a1f31225f98ef826b844be27` |
| `evidence/logs/expansion-assembly-02.log` | `2e271d4e482a0a1ad32d87d1f38826d0f6aad29a211982f927cdff15fb6b547f` |
| `.lake/build/lib/lean/MF21Restart/ExpansionAssembly.olean` | `4038a96694adb0c0cddc81f988a198c1f5e139d3ce2d6ddae54729e0dd6a7522` |
| `MF21Restart/ImplicitExpansionBounds.lean` | `53ac303b8ee106c09898d46716c75ee28e0b0207342996dd68d3dcc3255bf955` |
| `evidence/logs/implicit-expansion-bounds-01.json` | `1458a2d6f727f65e26b34ea35b269d77081485bfca35861e18dca73f65fd302a` |
| `evidence/logs/implicit-expansion-bounds-01.log` | `88227459f426d84741ee6775d90b5ac9416cbf6ad2b99e2d930ec3421213173e` |
| `.lake/build/lib/lean/MF21Restart/ImplicitExpansionBounds.olean` | `241720354bc23f08237a3a779dd7050c5eeaee703ed82e70e87ced977a9b116f` |

The logs contain 3, 2, and 2 public theorem axiom reports, all exactly
`propext`, `Classical.choice`, and `Quot.sound`. Project import-closure
scans (3, 4, and 73 modules) found no proof-side `sorry`, `admit`, custom
`axiom`, `native_decide`, or `unsafe` marker, and no Challenge import.
No Comparator or GitHub final verification is claimed.
