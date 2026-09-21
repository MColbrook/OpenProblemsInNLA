# Independent review: actual determinant conjugation and normalizer

Verdict: **APPROVE the stated intermediate results.** No material source-fidelity
or proof defect found. This is not approval of a complete MF-21 proof or of an
unrun Comparator check.

Reviewer: `/root/mf21_restart_lean_audit`, 20 September 2026. The coordinator
authored `BoundaryConjugation.lean`, `RootListProducts.lean`, and
`BoundaryNormalizer.lean`; this reviewer did not edit them or run a compiler.
The review follows the pinned `REFEREE_STANDARDS.md`, SHA256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Exact reviewed sources

All paths below are relative to the MF21-restart project. SHA256 values were
computed from the actual files during this review.

| Source or statement lock | SHA256 |
|---|---|
| `MF21Restart/BoundaryConjugation.lean` | `0327b3279564ebc620e67657668f474bc2c3a23514df6e95cf74b159fb8bdc9c` |
| `BOUNDARY_CONJUGATION_STATEMENTS.md` | `60ec0c241b839f41ba384d0658734752c35e6ede9b288d32dd787217f8ec0351` |
| `MF21Restart/RootListProducts.lean` | `331f649581125568a45313aea57d79342c4362ae1efb4d0dad1f5ff64f91c75e` |
| `ROOT_LIST_PRODUCT_STATEMENTS.md` | `14bb7df399d047b7548576c54ab51fe984645777f711c03308c3c501282d4c72` |
| `MF21Restart/BoundaryNormalizer.lean` | `7309e2650c79b925f4f4bb158b2b4fc435def898012e399d6b20d83579e8d3b6` |
| `BOUNDARY_NORMALIZER_STATEMENTS.md` | `0740f0988d0b3cad282be8c6ebfda37a9ac8bfa0bc3c0adf6f3b5a58e2ecc7f0` |

The inherited-order/sign support file `MF21Restart/LeadingBoundaryIndices.lean`
was also read in full to check the literal minus sign in the normalizer:
SHA256 `cccc3c1efd31bcd7a7bb3c9e7f63b6414f79537098ca4ee7885ce613df02833c`;
its lock has SHA256
`bf00a513fa59f03919a9a16ec6ee5c02603f1270aba60fd4770a608a7992800a`.
This auxiliary sign review is not an independent review of this reviewer's
own imported root or phase proofs. In particular, `PhaseProduct.lean`
(`1a4e719778fff8ed729c9bb6cc5f7615cf5d2aa0696b8df302c107afd64afeb1`)
and this reviewer's `CharacteristicRoots`, `StableRootSymmetry`, and
`RealComplexEigenvalue` are excluded from the independent authorship scope.

Source-fidelity references:

- `original-proof/solution.md`, SHA256
  `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`,
  lines 142–188 and 192–215, equations (13)–(18).
- `MF21Restart/Definitions.lean`, SHA256
  `35a74047a81a9b7526e9bf039880ca8f07ae33314e2b5b960ab254e02fca4b51`,
  lines 18–25 and 38–53: actual symbol, Fourier Toeplitz matrix, and one-based
  sorted eigenvalues.
- `MF21Restart/BoundaryExpansion.lean`, SHA256
  `bc873ac5a5cb569d3dda0bc3b6ecf623e09d326f0d82cd613fdc3149c24a3979`,
  lines 20–35: actual matrix and coefficient conventions.
- `MF21Restart/ConcreteBoundary.lean`, SHA256
  `bde3c2195d13e981249f6eebf9691b05d1f186edad7aa7b9e72c133f911063f4`,
  lines 10–30: the already constructed determinant and finite eigenvalue
  bridge; lines 47–62: the separate artificial zero at pi.

## Mathematical and statement findings

1. **The conjugation permutation is explicit and has the correct sign.**
   `BoundaryConjugation.lean:10–28` transports the block permutation from
   `(Fin(m-1) + Fin 2) + Fin(m-1)` to the literal `Fin(2*m)` ordering.
   The two identical reversal signs multiply to one; the distinct middle
   transposition contributes minus one. No parity restriction on m appears.
   Lines 30–102 check each block against the actual root definitions,
   including the index identity `m-(ell+1)=ell.rev+1`. There is no assumed
   permutation or assumed determinant symmetry.

2. **The matrix convention and conjugation conclusion match (13).**
   At `BoundaryConjugation.lean:104–123`, conjugation acts on columns of
   `boundaryMatrix m n (characteristicRoots m theta)`, leaving its row powers
   unchanged. The top powers are 0 through m-1 and the bottom powers are
   n+m through n+2m-1, as required. The determinant permutation formula
   proves `conj D=-D`, then `D.re=0`. These conclusions hold for every real
   theta and every natural n when m>=2, including singular endpoint matrices.
   There is no determinant nonzero assumption or eigenvalue assumption.

3. **Q is the exact product, real and positive, not an assumed modulus.**
   `RootListProducts.lean:10–57` identifies the actual exterior indices
   `m+1,...,2m-1` with `ell+1`, ell in `Fin(m-1)`. The product identity
   preserves multiplicities and accounts for the entire exterior index set.
   Lines 59–87 prove conjugation invariance, Q(0)=1, and positive real part
   for theta>=0 and m>=2. Positivity follows from continuity and the proved
   global nonvanishing, using the intermediate value theorem. No sign choice
   or positive-root premise is hidden in the statement. The m=2 list has one
   entry, and the same proof applies. Empty smaller lists do not affect the
   m>=2 normalizer conclusions.

4. **The Vandermonde argument proves the needed reality of the product.**
   `RootListProducts.lean:89–112` conjugates a Vandermonde by the row reversal
   of its actual root list. Each determinant acquires the same reversal sign;
   their product is fixed by conjugation. It correctly does not assert that
   either Vandermonde separately is real or positive. The root-row versus
   boundary-column Vandermonde conventions agree under transpose, whose
   determinant is unchanged.

5. **The normalizer is literally (16) with sigma=-1.**
   `BoundaryNormalizer.lean:61–66` defines
   `(-2*i) V(R)V(O) Q^(n+m+1) normSq(f)`. Here `normSq(f)` is exactly |f|^2.
   The exponent is n+m+1, not n+m. The selected Splus sublist is `(z,O)` and
   its complement is `(R,z-inverse)`; `LeadingBoundaryIndices.lean:74–128`
   proves those inherited index orders. Lines 130–221 establish that Sminus
   has sign +1 and Splus sign -1 by the actual column equivalences. As a
   direct parity check, Splus replaces the first bottom-block index m with
   m-1, making the bottom-row-plus-selected-column index sum odd for every
   m>=1. Thus the minus sign is consistent with the manuscript's otherwise
   unspecified sigma. This sign check does not replace the still separate
   leading coefficient factorization.

6. **Smoothness and nonvanishing use the actual factors, including pi.**
   `BoundaryNormalizer.lean:11–59,68–96` derives separate stable/exterior
   list injectivity for 0<theta<=pi from the actual stable roots. It never
   assumes full root-list injectivity at pi, where the two unit roots coincide.
   Both Vandermondes, Q, and f are individually proved nonzero on this domain.
   `normSq` is expressed through real and imaginary parts in the smoothness
   proof, so no differentiability of absolute value at its zeros is assumed.
   Global real `ContDiff` is established for the literal function. Nonvanishing
   is correctly not asserted at theta=0.

7. **The real quotient and eigenvalue criterion have the right scopes.**
   `BoundaryNormalizer.lean:98–115` proves `conj N=-N` and therefore D/N is
   real. The reality statement is valid for all real theta, including zeros
   of N, because field division is totalized there; it does not imply a
   nonzero denominator at zero. Lines 117–123 state the meaningful eigenvalue
   equivalence only for 0<theta<pi, where N is nonzero and the actual
   determinant bridge applies. The left side uses `1<=j<=n` and the original
   sorted eigenvalue function, so no zero-based indexing or out-of-range
   totalized value is introduced. The n=0 case has an empty eigenvalue index
   range and is covered by the already established finite-matrix bridge.

## Proof/trust and computation scope

No `sorry`, `admit`, custom axiom, unsafe declaration, or `native_decide` occurs
in the three reviewed modules. A read-only scan of their project import
closure found none of these proof-side markers and no `Challenge` import.
The proofs use ordinary algebra, finite permutations, continuity, the
intermediate value theorem, and existing Mathlib determinant APIs. No numeric
certificate, subset enumeration, or unproved asymptotic input is introduced.
The finite `fin_cases` on the two oscillatory positions only verifies a
two-element permutation.

These modules do not prove `D/N = sin(F)+E`, identify the chosen error-sum
coefficients with the literal quotient, prove E real or E(pi)=0, establish
ordered-root localization, or prove the complete Target. Their statements
and locks explicitly leave the assembly identity separate. No original
target count increases.

## Actual local evidence and precise provenance limits

The reviewer ran no Lean process. The following existing records were read,
and the listed hashes were independently recomputed.

`RootListProducts` has an actual successful execution record
`evidence/logs/root-list-products-01.json`, SHA256
`38a63efc00a5ce04d9a76e45b589b36eb73888a53b16268a41aec92b30cc79e9`.
Its command is `lake env lean -j1 -M4096 -o
.lake/build/lib/lean/MF21Restart/RootListProducts.olean
MF21Restart/RootListProducts.lean`; exit_code=0 and source_unchanged=true.
The record's source, log and output hashes all match current files:

- log: `05349e6b5325e3eb2bf90fc827c9662ceef83ab1b87d3df4a39f7408fd561873`;
- output: `e577183afc4c5987c98eeb9c4eac2843c604d45683a8159b5e396273162f21ee`.

The auxiliary `LeadingBoundaryIndices` successful execution JSON also matches
its current source, log, and output, records exit_code=0/source_unchanged=true,
and uses the same one-thread/4096-MiB options. Its JSON SHA256 is
`fccf9942d589ae7aff4ea87bb796674671a2c04512ae4a5594e82dbc81ec0158`;
log `bf73e7fc8d8eb977b3b378631a2a6a0a2f58f4fa0907ffb57d0c126fa05d1ca5`;
output `091bf621576424c259b34887475310b3cba8034f1ebf07811f323cfd34c0ace0`.

The coordinator reported actual exit-code-zero runs for
`boundary-conjugation-02.log` and `boundary-normalizer-02.log`. This reviewer
verified that these logs exist and contain respectively four and eight
axiom reports with no error lines; every reported axiom is among
`propext`, `Classical.choice`, and `Quot.sound`. The RootListProducts and
LeadingBoundaryIndices logs each contain seven reports with the same scope.

Unlike the two JSON-backed tests above, **the Conjugation02 and Normalizer02
tests have no per-test JSON recording their source/output hashes or exit
status**. The current artifacts are:

| Artifact | SHA256 |
|---|---|
| `evidence/logs/boundary-conjugation-02.log` | `dae5cff9f1772c3e1b76eb63adca1338ab0967da22207f649e41220ce17fdfeb` |
| `.lake/build/lib/lean/MF21Restart/BoundaryConjugation.olean` | `a27a44f2fd05d1cdb6f001c749a8e261cfef09f6cff64dcd28e68b93bf2e9073` |
| `evidence/logs/boundary-normalizer-02.log` | `9f40409f3d0044275b62e844b9a3ec407dd2ac3a938facb09e30f233a5aed116` |
| `.lake/build/lib/lean/MF21Restart/BoundaryNormalizer.olean` | `56d8f3b3732c3832bfa8fb3efd7fe1e976dcd9d792ed75177b7e92df8c23a0cd` |

Consequently the static mathematical approval is independent, while exact
source-matched local build provenance for those two modules still relies on
the coordinator's reported direct run until the promised integrated run
records it. Artifact presence alone is not treated as proof of that provenance.
No GitHub Comparator/kernel/sandbox run has been performed or approved here.

## Integrated evidence addendum, 20 September 2026

The later actual integrated record closes the two source-provenance gaps
identified above. The reviewer independently read
`evidence/runs/20260920T213250267591Z/record.json`, SHA256
`799347e39236dd1cee0031b54fd987f7e83e03666e668895715615e3103fc3a2`,
which is byte-identical to the current `evidence/latest-local.json`.
It records 71 serial module runs, all exit_code=0, with one thread and
4096 MiB. All 71 recorded source hashes, all three pin hashes, all log
hashes, and all output hashes match the current files. The runner hash
also matches the current `verify_local.py`:
`4ee6415166fc0f9c9c35d16540c1fc16060d02a7663bc44bd2f1248881169fdf`.
Its completion checks compare every source and pin again before recording
success. Every one of the 236 reported axiom sets is contained in
`{propext, Classical.choice, Quot.sound}`.

In particular, the record explicitly links the already reviewed
BoundaryConjugation source hash `0327b3279564ebc620e67657668f474bc2c3a23514df6e95cf74b159fb8bdc9c`
to `BoundaryConjugation.log` hash
`dae5cff9f1772c3e1b76eb63adca1338ab0967da22207f649e41220ce17fdfeb`
and output hash
`a27a44f2fd05d1cdb6f001c749a8e261cfef09f6cff64dcd28e68b93bf2e9073`.
It links BoundaryNormalizer source hash
`7309e2650c79b925f4f4bb158b2b4fc435def898012e399d6b20d83579e8d3b6`
to `BoundaryNormalizer.log` hash
`9f40409f3d0044275b62e844b9a3ec407dd2ac3a938facb09e30f233a5aed116`
and output hash
`56d8f3b3732c3832bfa8fb3efd7fe1e976dcd9d792ed75177b7e92df8c23a0cd`.
Both runs use the recorded `lake env lean -j1 -M4096 -o ...` command and
`LEAN_NUM_THREADS=1`. These are now source-matched successful local runs;
the earlier historical absence of per-test JSON is no longer an outstanding
provenance limitation. This addendum does not expand the semantic review
scope or independently review this reviewer's own imported proofs.

The integrated record explicitly says `comparator: not_run` and has no
GitHub run ID. It covers partial components only, with Target unproved;
its run count and axiom-report count are not counts of original targets.
