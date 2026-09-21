# Independent review: concrete simple residual roots

Verdict: **APPROVE** the six stated intermediate results. The module
correctly turns a simple zero of the actual scalar residual into a
one-dimensional actual Toeplitz eigenspace and a unique one-based index.
The simple-zero assumptions are explicit premises of this bridge; the
module does not establish roots in phase cells or identify the unique
index with a cell label.

Reviewer: `/root/mf21_restart_lean_audit`, 20 September 2026. The reviewer
did not author or edit this module and ran no compiler. Review follows
the pinned `REFEREE_STANDARDS.md`, SHA256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Exact source and local evidence

| Artifact | SHA256 |
|---|---|
| `MF21Restart/ActualSimpleRoots.lean` | `fd2b696d326d7672d791d41c1368a2b8cfd0a2c8fc1737f32c36a591bd95f6f8` |
| `ACTUAL_SIMPLE_ROOTS_STATEMENTS.md` | `a70e6e5ed2c4a008824e8bad9792e1020299d943ee93a4e172aecc82c7e248ed` |
| `evidence/logs/actual-simple-roots-02.json` | `820846a1a8c3045565709cd3a38562354149c99e16997378b5b31fe8936d9465` |
| `evidence/logs/actual-simple-roots-02.log` | `94b4e6b3aef5ac38b96097c7db366674178e3f69482f4c131122ac328ed0c395` |
| `.lake/build/lib/lean/MF21Restart/ActualSimpleRoots.olean` | `0c5bb9064394847dd95ff8c32dd96f1bba80e6bf6d4abffc27d539a9fc421bd2` |

All hashes were independently recomputed. The execution record matches
the current source/log/output triplet, records exit_code=0 and
source_unchanged=true, and gives `LEAN_NUM_THREADS=1` with the command
`lake env lean -j1 -M4096 -o
.lake/build/lib/lean/MF21Restart/ActualSimpleRoots.olean
MF21Restart/ActualSimpleRoots.lean`. The six axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`. This is actual local
development evidence, not a Comparator run.

The manuscript comparison is `original-proof/solution.md`, SHA256
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`,
line 239: a simple zero of the determinant gives a one-dimensional
eigenspace, and Hermitianity gives algebraic multiplicity one.
The preceding normalization is in Lemma 3, especially lines 208–215.

## Findings

1. **The residual is concrete and its derivative is ordinary.** Lines
   22–32 define precisely `sin(manuscriptPhaseFn)+manuscriptError` and
   derive `cos(F)*F'+E'` from the previously established differentiability
   of these two actual functions. The interval includes both endpoints
   because the reused hypotheses concern ordinary differentiability,
   not merely differentiability within the interval. No derivative
   formula or bound is added as a premise.

2. **The boundary matrix is the actual matrix.** Lines 34–46 prove its
   smoothness entry by entry. The row split is `row<m`, with upper powers
   `row` and lower powers `n+row`, exactly as in
   `BoundaryExpansion.lean:20–22`. Thus the lower exponents begin at n+m,
   not n or n+m+1. The actual characteristic-root smoothness theorem is
   used for each column. The locally scoped elaborator transparency
   option does not change a proposition or introduce a trust axiom.

3. **The normalizer identity retains its phase and sign.** Lines 48–57
   use the exact previously proved quotient and reality identities,
   followed by proven nonvanishing of the literal normalizer on
   `0<theta<=pi`. The result is `D=N*H`, with H the real residual cast to
   complex. There is no absolute value, arbitrary normalizer, or sign
   choice replacing the determinant. The normalizer's denominator is
   justified before multiplying back.

4. **The determinant derivative uses a neighborhood identity.** Lines
   62–77 restrict to `0<theta<pi`. The open interval is a neighborhood of
   theta, and `D(t)=N(t)*H(t)` holds throughout that neighborhood.
   Differentiating this product gives `N'*H+N*H'`; the stated zero of H
   removes the first term at theta. `HasDerivAt.congr_of_eventuallyEq`
   transfers the derivative to D. The proof does not infer derivative
   equality from a single pointwise equality. The derivative of the real
   residual is correctly included into complex scalars via `ofReal_comp`.

5. **The simple-zero bridge discharges every root-list condition.** Lines
   79–101 combine the actual matrix derivative, the actual determinant
   derivative, and nonzero `N(theta)*H'(theta)`. The two factors are
   separately nonzero by the proved normalizer theorem and the explicit
   simplicity premise. The determinant itself is zero by D=N*H.
   `characteristicRoots_injective`, `characteristicRoots_ne_zero`, and
   `characteristicRoots_equation` discharge the generic finite boundary
   lemma's conditions for the actual ordered roots and actual symbol.
   Root distinctness, characteristic equations, matrix rank and
   eigenvalue multiplicity are conclusions of prior proofs, not new
   hypotheses here. The open upper endpoint excludes the artificial
   determinant zero at pi, where the two unit roots coincide.

6. **The conclusion counts the original index range.** Lines 105–111
   use the already proved equality between complex geometric dimension
   and multiplicity in the actual sorted real eigenvalue list. The result
   is exactly `exists unique j, 1<=j and j<=n and eigenvalue m n j=symbol m theta`.
   No zero-based or out-of-range totalized value participates. This is a
   unique position for a simple eigenvalue; it says nothing about the
   phase label of that position. For n=0 the simple-zero premises cannot
   hold, consistently with the zero-dimensional Toeplitz eigenspace.

The interfaces checked in this assembly review are unchanged:

| Imported source | SHA256 |
|---|---|
| `MF21Restart/SimpleDeterminant.lean` | `14221eca53ecb544043c81acffe32691f740afd2ffdeaa34c5fec4f2a6cfade1` |
| `MF21Restart/EigenvalueMultiplicity.lean` | `d2cd938bd1fbbf405f8c2645d38224cfbbf66df058318d11eababe2ecec71bd1` |
| `MF21Restart/ConcreteBoundary.lean` | `bde3c2195d13e981249f6eebf9691b05d1f186edad7aa7b9e72c133f911063f4` |
| `MF21Restart/BoundaryNormalizer.lean` | `7309e2650c79b925f4f4bb158b2b4fc435def898012e399d6b20d83579e8d3b6` |
| `MF21Restart/DeterminantRemainder.lean` | `3ff379de253810a3edaf355a243e26981c46d0052ca636aac5ace9b82bb6f318` |

In particular, `SimpleDeterminant.lean:9–28` proves kernel dimension one
by nonzero kernel at a zero determinant and impossibility of dimension
at least two when the determinant derivative is nonzero. Its lines
30–43 transfer this through the finite recurrence/boundary equivalence.
`EigenvalueMultiplicity.lean:79–108,112–139` supplies the actual Hermitian
multiplicity and one-based uniqueness bridge. These match the uses above.

## Trust and scope

A read-only scan of the 49-module project import closure found no `sorry`,
`admit`, custom axiom, unsafe declaration, `native_decide`, or import of
`Challenge`. This module adds no numerical certificate or approximation.
Its six statements agree with the prior lock, and no material change is
requested.

This independent review covers the new assembly and its use of the
imported interfaces. It does not independently re-review this reviewer's
own root, Fourier recurrence, phase-product, or error-bound proof internals.
Existence and uniqueness of a residual zero in any phase cell, the final
top-down ordering argument, and MF-21's full asymptotics remain outside
the result. No completed original-target count or unrun GitHub Comparator
success is claimed.
