# Independent referee B: circulant ordering and actual interlacing bounds

Verdict: **APPROVE within the four-module scope below.** I independently read the final sources, their prior statement locks, the unchanged manuscript, and the retained successful local evidence. I did not run Lean or change these sources. No material correctness or source-fidelity issue was found.

The reference is the frozen MF-21 manuscript, SHA-256 `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`, especially the circulant paragraph and equations (21)–(22), lines 259–277, their finite-prefix use at line 306, and the reciprocal-tail use at line 358. The review applies `REFEREE_STANDARDS.md`, SHA-256 `e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Mathematical statements and proofs

### Complete ordered circulant spectrum

`CirculantOrder.lean:18` defines the literal one-based formula `symbol m (2*pi*floor(j/2)/N)`. Its totalization at indices outside `1,...,N` is not used to assert spectral values there. The frequency permutation at lines 21–47 is a genuine bijection on all of `Fin N`; it orders frequencies as `0,1,N-1,2,N-2,...`. The reflected values agree by the actual cosine formula for the symbol, not by an assumed symmetry of an unspecified spectrum.

The even-size final frequency `pi` occurs once. For odd size, both members of the largest pair remain. The first frequency is zero. No conjugate pair is collapsed and no distinct-eigenvalue set replaces a multiset. `fourierCirculant_charpoly_real` and `fourierCirculant_charpoly_ordered` transport the already proved characteristic polynomial of the actual circulant and reindex its entire product. `fourierCirculant_sorted_eigenvalues` at line 121 identifies characteristic-root multisets and then their increasing lists. Its monotonicity proof uses only frequencies in `[0,pi]`. Repeated eigenvalues therefore have the correct multiplicity.

### Proved finite-dimensional interlacing

`DiagonalInterlacing.lean:114`, `diagonal_isometry_interlacing`, is a genuine generic intermediate theorem. Its two premises are exact identities for squared norms and diagonal quadratic forms. They are not eigenvalue inequalities, and the subsequent actual matrix theorem discharges both.

For the lower inequality, lines 50–105 map a space of dimension `j.val+1` into the `j.val` lowest ambient coordinates. The kernel contains a nonzero vector. Literal extension by zero preserves its nonzeroness, and the sum of its squares is strictly positive. Its principal form is at most `a j` times that sum, whereas its ambient form is at least `b j` times the same sum. Cancellation proves the lower inequality. This argument allows negative and repeated values and has no hidden definiteness premise.

For the upper inequality, reversing and negating both arrays preserves the two exact identities. The explicit arithmetic at lines 160–169 proves that the reversed ambient position is `j.val+(N-n)`, rather than merely a nearby index. The empty principal dimension has no in-range assertion; the theorem remains meaningful there.

### Actual Hermitian matrices and their original ordered lists

`HermitianInterlacing.lean:20` defines increasing eigenvalues by reversing the pinned spectral theorem's decreasing enumeration. `hermitianAscendingValue_sorted` at line 37 proves equality with the sort of the actual matrix eigenvalue multiset, using equality of the linear-map and matrix characteristic polynomials. It does not assume that the two potentially different enumerations coincide termwise.

The coordinate equivalence at lines 67–103 uses the actual orthonormal eigenbasis. Its norm statement is explicitly a sum of squares: it does not confuse the ordinary function-space norm with the Euclidean norm. The quadratic identity is the actual expression `sum_i (A.mulVec x i)*x i`. The zero-extension identities at lines 105–149 prove that exactly the initial principal block contributes.

`hermitian_principal_interlacing` at line 153 constructs the map as ambient eigen-coordinates composed with zero extension composed with inverse principal eigen-coordinates. It then proves both hypotheses of the generic diagonal theorem. The only matrix-compression premise is the literal leading principal-block equality. There is no assumed min-max result, spectral comparison, simplicity, or positivity.

### Exact manuscript indices and constants

`CirculantBounds.lean:18–39` identifies these increasing enumerations with the unchanged Toeplitz eigenvalue list and the proved circulant list. The final conversion fixes the earlier dependent-list elaboration issue by proving `List.ofFn (orderedEigenvalue m n)=orderedEigenvalueList m n`; it does not change the enumeration.

`eigenvalue_circulant_interlacing` at line 41 instantiates the actual block equality with `N=n+2*m` and `i=j-1`. Its explicit arithmetic gives lower position `j` and upper position `j+2*m`. Thus it proves exactly (21) for every `1<=j<=n`, retaining all multiplicities and both endpoint indices.

The sine estimates at lines 64–111 use the proved interval `0<=pi*floor(j/2)/N<=pi/2`. They give the stronger explicit upper bound `(pi*(j+2*m)/(n+2*m))^(2*m)` and the first lower bound of (22). `eigenvalue_circulant_lower_bound` at line 113 uses `j<=3*floor(j/2)` only for `j>=2`, giving the second lower bound of (22). The lower bound at `j=1` is correctly zero and is not used to dominate that reciprocal term.

`eigenvalue_fixed_prefix_bound` at line 129 proves the needed estimate for every fixed natural `J`, including the vacuous `J=0,1` cases. It uses actual spectral positivity to remove the absolute value, and takes the positive constant `(pi*(J+2*m))^(2*m)` and threshold `N0=1`. The comparison `n+2<=n+2*m` is valid for the stated `m>=1`. The resulting estimate is exactly in powers of `h=1/(n+2)`, with `1<=j<J` and `j<=n` explicit.

`eigenvalue_reciprocal_tail_majorant` at line 166 derives

    h^(2*m)/eigenvalue m n j
      <= (3*m/4)^(2*m) * ((j:Real)^(2*m))^(-1)

for every `2<=j<=n`, from the positive lower bound and `(n+2*m)/(n+2)<=m`. All denominators are proved positive before division. The final eventual version at line 202 chooses this same positive constant and `N0=1`. It assumes neither an inverse asymptotic nor a trace limit. The first reciprocal term remains separate, as required by the manuscript.

## Dependency and computational scope

The four reviewed modules contain no custom axiom, `sorry`, `admit`, unsafe shortcut, numerical approximation, or LeanCert computation. Their arithmetic uses symbolic inequalities, finite sums, and standard kernel-checked tactics. A bounded search of the pinned Mathlib matrix, inner-product, and linear-algebra matrix directories found no ready interlacing/min-max declaration; the general diagonal-form and real Hermitian proofs are appropriate reusable infrastructure rather than an assumed missing theorem.

This review relies on the previously proved actual `CirculantEmbedding` and `CirculantSpectrum` interfaces. I also read those sources to check that the principal block is the unchanged integral-defined Toeplitz matrix and that the characteristic polynomial uses a full invertible Fourier/Vandermonde matrix. This report's independently pinned test scope is the four modules below. My own earlier `SpectralOrder` and `SpectralEnclosure` proofs are dependencies, not work independently re-reviewed by me here; their separate referee coverage remains relevant.

These results discharge the actual finite-prefix and reciprocal-tail spectral estimates. This report does not independently review my own final `TargetProof`, the full asymptotic assembly, or the final Comparator configuration.

## Exact source and local evidence

I recomputed every source, lock, retained record, log, and output hash below. For each module the current source, log, and `.olean` match its record; the record reports `exit_code=0` and `source_unchanged=true`.

| Module | Source SHA-256 | Prior statement-lock SHA-256 |
|---|---|---|
| CirculantOrder | `b2fefbff57d6567cef75d9b1c92902147612a67b48de6255d9e358797ecbda0c` | `696fa0fa92f8d081bae064ede6c80c48fb7b09e5a38b742544ac60022246472f` |
| DiagonalInterlacing | `b8eb5b0c72c15e1f8caf2b657311b6e7be925e225bfe33b110aa535a6183b345` | `e6e7ca3a6183b438e712da13b2aaaf2628d6eb147fab8fdc4bc38e0798e686b5` |
| HermitianInterlacing | `b2f99448fd17409d3873c94a4d2a6e4e8d7ce1359e0764121d269065b5be30e2` | `d278b61365691a0263afdbf88bc5d7d2a66461bdceee08eac86fc5ed0df265ae` |
| CirculantBounds | `f63c776c46312d11347199ae3eb42003725dd95c578012b72f490fbb9a2a86ff` | `60660a5af678ccabce1042377083c96600070626b61476382a1e5c663537f5b6` |

The statement locks are respectively `CIRCULANT_ORDER_STATEMENTS.md`, `DIAGONAL_INTERLACING_STATEMENTS.md`, `HERMITIAN_INTERLACING_STATEMENTS.md`, and `CIRCULANT_BOUND_STATEMENTS.md`.

| Retained record under `evidence/logs/` | Record SHA-256 | Log SHA-256 |
|---|---|---|
| `circulant-order-02.json` | `8480af635170b40c8632edea3c28c14727049c9665cdbc58a2664b83b401edc2` | `d0e2819ac9f5cd460606eec1e7b8b3a71cf1e0461aa2373f190ea5f17fdbd32a` |
| `diagonal-interlacing-03.json` | `9c6e1cc774998c801144ae3e0137e8e53d2c92fcb0cf9945424e8e1c1c2ee437` | `a3ddceb0e5fb2bb55799975e6e84a98ffca75eb13ea89729b5c820b3c1c51d7b` |
| `hermitian-interlacing-02.json` | `b7d9c40d4ca4661db20c2fe1ec86380fb39c8cfe7aaac1ec3f62ccf049cab10f` | `4220d9a80a9fec8e014ff38fa0b68114fcb76f694e851ea5dcd5e9ae29fb258e` |
| `circulant-bounds-02.json` | `c15e7b6ebab87bb9c84ddc9c7aa02985804e8ef45d00e6e817b7610d62b41cbf` | `8dfa147e85fdff460c368737f751a26052635b6d0b376c8a47e4d0a38e8725cd` |

| Module output under `.lake/build/lib/lean/MF21Restart/` | Output SHA-256 | Standard-only axiom reports |
|---|---|---:|
| `CirculantOrder.olean` | `1afeeb0ae5eb00b926864eca6b7600dab76d564865a6c4deb064970a6571f983` | 4 |
| `DiagonalInterlacing.olean` | `418ba5d0344445d510b8fa6a479904b62ddfb5096f9ca27655b99f12b088314b` | 1 |
| `HermitianInterlacing.olean` | `5fd072330a17d26a8ab4f3112a8fbce23929a8768915ed45b06b60a0cabfe917` | 3 |
| `CirculantBounds.olean` | `347d4c86ecf65795898fd3cf4ac3ab3e766e873410e3ad45071b57931e3c4077` | 6 |

Each recorded command, run by the coordinator from the MF21-restart directory, has the exact form

    env LEAN_NUM_THREADS=1 lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/MODULE.olean MF21Restart/MODULE.lean

with `MODULE` replaced by the corresponding table entry. All fourteen actual log reports list only `propext`, `Classical.choice`, and `Quot.sound`. The remaining messages are unused-variable/simp/tactic linter warnings and do not change the statements.

This is inspected, source-matched coordinator local evidence. It is not a referee compiler run or a GitHub Comparator run. No unrun check is asserted successful.
