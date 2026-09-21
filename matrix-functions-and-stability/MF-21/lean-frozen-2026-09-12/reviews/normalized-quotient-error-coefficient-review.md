# Independent normalized quotient and error-weight review

Verdict: **APPROVE**, for `NormalizedQuotient.lean`,
`NormalizedErrorCoefficient.lean`, and the four supporting
`CharacteristicSublist.lean` results at the exact hashes below. The
sources prove regularity and actual uniform bounds for the defined
coefficient ratios and phase-adjusted weights. Identification of those
weights with the full displayed denominator in manuscript (18) remains
a separate leading-coefficient algebra obligation, explicitly preserved
in the lock.

Reviewer: `/root/mf21_restart_lean_audit`, 20 September 2026. I did not
author or edit these three modules. I independently read their complete
sources, locks, final successful logs and records, the actual imported
normalized coefficient definitions, and the manuscript. My own imported
characteristic-root and tangent proofs are excluded from independent
proof-review scope; their use here was checked against their statements.
I ran no compiler. The pinned referee standard has SHA-256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Exact reviewed sources

Paths are relative to `MF21-restart`.

| Path | SHA-256 |
| --- | --- |
| `MF21Restart/CharacteristicSublist.lean` | `29ec8cd3beec7b1ec5b60a8788961fc755f1620975a35dfead59cce82acb8448` |
| `CHARACTERISTIC_SUBLIST_STATEMENTS.md` | `bb1b324365a571ffd4f61d21453067b6e25f5a098ae4a36ccff0718e5f76199e` |
| `MF21Restart/NormalizedQuotient.lean` | `64b0c557994407c92cc1247d11d2701b2b3435acb966c9dabf95da9ddcb3863c` |
| `NORMALIZED_QUOTIENT_STATEMENTS.md` | `d6200aa5ac387f122e08ddca8e19d7733a0e11c13a691a6859384e4accea0adb` |
| `MF21Restart/NormalizedErrorCoefficient.lean` | `196098a5618651861b2d92ff8ce145b2e7425092241b97ed908a07b2bb85c52d` |
| `NORMALIZED_ERROR_COEFFICIENT_STATEMENTS.md` | `8a4c5f3b73ebba879c598929ff2675b1104c3c33627fa09f36411af2fd8ca5a8` |
| `MF21Restart/NormalizedBoundary.lean` | `3d45a02be0ce050f37be4ec3db227504028730c9283f4148d5739b37c48a9261` |
| `MF21Restart/BoundaryProductDecay.lean` | `f9f9b6b0d5c8b8842049f91850a3cb6d4482747443c1448d1c1e325bdcd0d0e3` |
| `original-proof/solution.md` | `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa` |

## Denominator nonvanishing through pi

`CharacteristicSublist.lean:8–49` proves that for `0<theta<=pi`, equal
actual root values imply equal indices or the two oscillatory positions.
The stable, unit, and exterior groups are separated by their norms;
within stable and exterior groups, the proved stable-root injectivity
applies through pi. The source does not falsely use full root-list
injectivity at pi.

Lines 51–61 show an injective index sublist remains a list of distinct
root values if it does not contain both oscillatory positions. Lines
63–75 combine that fact with the exact Vandermonde factorization at
positive theta, and separately use the distinct actual tangents at
zero. This establishes nonvanishing of the normalized sublist
Vandermonde on the entire closed interval.

Lines 77–98 apply the argument to both a cardinality-m subset and its
complement. The hypothesis `a in s iff b notin s`, for the actual z and
inverse-z positions a,b, means exactly one is in s. It therefore also
separates them in the complement. Both inherited-order embeddings are
injective and the actual Laplace sign is nonzero. This proves the
normalized denominator is nonzero; it is not a new nonvanishing premise.
The separation condition is necessary at pi and is satisfied by the
actual leading set. Subsets placing both oscillatory positions together
would instead have a zero Vandermonde at pi.

## Exact quotient and ordinary derivative bounds

`NormalizedQuotient.lean:10–12` divides two actual normalized boundary
coefficients of cardinality-m subsets. Lines 14–22 prove agreement with
the quotient of the original raw coefficients for theta!=0 by cancelling
their proved common power. This restriction is correct: at zero the raw
coefficients vanish for m>=2 and their totalized 0/0 is not the completed
ratio. No nonzero-denominator condition is needed for this algebraic
identity away from zero; its common scalar is nonzero.

Lines 24–31 prove `ContDiffAt` of the ratio at every point in `[0,pi]`,
using the just-proved nonzero denominator and the actual normalized
coefficient regularity. The conclusion is regularity in an ordinary
neighborhood of each endpoint, not just one-sided differentiability.
The function is allowed to have unrelated behavior outside the interval;
no global nonvanishing claim is made.

The helper at lines 33–49 first derives continuity of f and of its
ordinary real derivative from local `ContDiffAt`. It evaluates the
continuous Fréchet derivative at the fixed scalar one to obtain the
ordinary derivative's continuity. Compactness of `[0,pi]` supplies two
finite norm bounds, and their maximum with one is strictly positive.
Thus the bound is derived, not inserted as an equivalent hypothesis.
Lines 51–58 apply that general argument to the actual ratio. The
constant may depend on the two subsets at this stage, as its statement
honestly specifies.

## Phase-adjusted weights and uniformity across all subsets

`NormalizedErrorCoefficient.lean:11–12` defines the actual phase
multiplier

`U(theta)=exp(i*((m-1)*theta+2*manuscriptPsi(m,theta)))`.

The phase has the positive signs shown, and `manuscriptPsi` remains the
sum of individual arguments. For the m>=2 application, the natural
cast of m−1 is exactly the manuscript's real m−1. Lines 14–27 prove U
nonzero and locally real analytic on the closed interval by the existing
phase theorem and the actual complex exponential.

Lines 29–33 define the weight as the ratio of the normalized coefficient
of S to that of S+, divided by `2*i*U`. The leading set is the actual
exterior index set plus z; its cardinality and separation are proved in
`BoundaryProductDecay`. Lines 35–46 instantiate the quotient regularity
with those exact facts and prove the extra denominator nonzero from
`2!=0`, `i!=0`, and exponential nonvanishing. No denominator bound or
claimed removable singularity is an input.

The uniform theorem at lines 48–68 first obtains the proved value and
derivative bounds for each member of the finite type of all
cardinality-m subsets. It takes one plus the sum of their positive
constants. Each individual constant is at most that sum, so this gives
one positive constant chosen before **every** subset, its cardinality
proof, and theta. The constant depends only on m, as required for the
finite-sum application. This includes leading subsets too; that is a
valid strengthening of the eventual error-sum requirement. Finiteness
is used symbolically, with no enumeration or numerical oracle.

The signs are consistent with the pending leading-coefficient algebra:
if the z-leading coefficient has the manuscript form
`sigma*V(R)*V(O)*Q*z^(-(m-1))*conj(f)^2`, multiplication by U cancels
the z phase and turns `conj(f)^2` into `|f|^2`. That algebraic identity
must still be proved; this review does not treat it as an imported fact.
The current bound concerns the exact defined quotient weight, and the
lock explicitly separates its identification with (18)'s displayed
coefficient. Reality of the eventual summed error is also not concluded.

## Source-matched local evidence

All three retained records specify actual local commands of the form

```text
lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/<Module>.olean MF21Restart/<Module>.lean
```

They record exit code 0 and unchanged source. I independently rehashed
each current source, corresponding log, and compiled output; all nine
hashes match their records. The records and artifacts are:

| Artifact | SHA-256 |
| --- | --- |
| `evidence/logs/characteristic-sublist-01.json` | `38dbc962ccbe3b2048e8766eff6688bc0d9d3afa5f2aea39b269a5ef2b8c8c51` |
| `evidence/logs/characteristic-sublist-01.log` | `4a98cee186656389471b4ae7b27d1df40c3357b71e03221fcf638d6495c42588` |
| `.lake/build/lib/lean/MF21Restart/CharacteristicSublist.olean` | `fa65787b6aa29615a7d10bbd5d48b9bb79938fc6207bad0933db6842619fe8db` |
| `evidence/logs/normalized-quotient-03.json` | `a70ad8d8485136a8e95b5c7bbf263a7fa7d4cb7e76f5149a791622310d28b21d` |
| `evidence/logs/normalized-quotient-03.log` | `48b4f0eb52a963d48845b9b2654cc39590015499e7fdeb8e6c21908de7dbc3a6` |
| `.lake/build/lib/lean/MF21Restart/NormalizedQuotient.olean` | `4c7d30ef2c40b07e000d39d366e1110131a9fec721b17eb3e75549787dbdbcd5` |
| `evidence/logs/normalized-error-coefficient-02.json` | `d2e4d31818d3c0b52539ebe32596a1707e8a9e4653370115464392bf730308ed` |
| `evidence/logs/normalized-error-coefficient-02.log` | `a35de3fe6e97e50b04ff2743c8357cbda5da91b0a514cdca1da56d47c10d87f0` |
| `.lake/build/lib/lean/MF21Restart/NormalizedErrorCoefficient.olean` | `7e3c5d6b5645823218e0c73726eeaef36ef91f9bb8fd17865ca3128064f3592f` |

The successful logs contain four, four, and five standard-only axiom
reports respectively. In the last log, the first two are the existing
leading-set helper declarations imported from `BoundaryProductDecay`,
not five new distinct mathematical results. Earlier failed attempts are
not counted as successful evidence.

No `sorry`, `admit`, custom axiom, unsafe shortcut, `native_decide`,
Challenge import, or legacy import appears in the three reviewed
sources. No material correctness or fidelity change is requested.
This is approval of the exact partial ingredients, not a claim of the
full determinant identity, exponential error bounds, phase indexing,
complete MF-21 Target, or an executed GitHub Comparator check. No
additional completed original problem is counted.
