# Referee B: finite triangular inverses

Verdict: **APPROVE**, scoped to the seven printed declarations in
`MF21Restart/TriangularInverse.lean`. The reviewer did not author or edit
this source and ran no compiler. This is an exact finite algebraic
ingredient toward the cited inverse-kernel input, not a proof of the
kernel limit, trace limit, or original MF-21 target.

## Source and local evidence

| Item | SHA-256 |
| --- | --- |
| `MF21Restart/TriangularInverse.lean` | `07f55713eb4977c850e148c09943ef9cced5d75adc1b6d60362ecd40991ee319` |
| `TRIANGULAR_INVERSE_STATEMENTS.md` | `3ccb2b260d7a41e8f8a95dd24b5182590c41b9bf227aeb6da0ba32c3eacb0871` |
| `evidence/logs/triangular-inverse-03.json` | `3cc9cf94df95e329db70bde91c93bb30d8ae5e59cc1593b8c8cfe45fbf6921d2` |
| `evidence/logs/triangular-inverse-03.log` | `5774c495fc6385bdc11b8302a2b90a9ea05464b903d4f1940b3a7d2914863160` |
| `.lake/build/lib/lean/MF21Restart/TriangularInverse.olean` | `6d1a9f233a59c3665d9fe0beed6611a2a44616612aa1cc1fa5203b9b8b20c3b0` |
| Pinned Mathlib `RingTheory/PowerSeries/WellKnown.lean` | `59d05a437894699b9df0b59c5bbaf531c260845b86368e0f29c5481d508fabcb` |

The reviewer recomputed source, log, and output hashes and matched them
to the retained JSON. The record reports unchanged source, exit code 0,
`LEAN_NUM_THREADS=1`, and

```
lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/TriangularInverse.olean MF21Restart/TriangularInverse.lean
```

The observed log contains all seven expected axiom reports, each listing
only `propext`, `Classical.choice`, and `Quot.sound`. No GitHub Comparator
run is claimed. The manuscript hash is
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`;
the pinned referee rubric hash is
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Statement and proof review

The matrix at lines 16–18 has exactly the locked upper-triangular
column-minus-row convention. The conditional guards natural subtraction;
entries below the diagonal are zero rather than a spurious constant
coefficient caused by truncated subtraction. Multiplication in the public
theorem is actual matrix multiplication.

`powerSeriesUpperMatrix_one` (line 20) handles the diagonal and both
off-diagonal cases. `powerSeriesUpperMatrix_mul` (line 34) extracts the
formal coefficient convolution and keeps exactly `i<=k<=j`. Its explicit
bijection is `k ↦ k-i` onto the finite range `0,...,j-i`, with inverse
`r ↦ i+r`. The proof verifies that this inverse remains below `n` using
`j<n`. The identity `j-k=(j-i)-(k-i)` is used only on that guarded range.
For `i>j` every product summand vanishes. Thus there is no analytic
convergence assumption or finite-section boundary error in this step.

The two matrix identities at lines 93 and 100 use the proved
multiplicativity, followed by the two unit inverse laws. The imported
`invOneSubPow` is not an unproved inverse assumption: its pinned Mathlib
definition explicitly supplies the binomial power-series value, the
polynomial `(1-X)^m` as inverse, and proofs of both products. The present
source transports this already-proved formal-series identity to finite
matrices.

The binomial entry formula at line 107 requires `m>=1`, precisely where
`m-1` expresses the positive-order binomial formula. The definitions and
both inverse laws remain valid at `m=0`, when both matrices are identities.
The coefficient formula at line 115 derives the sign `(-1)^k` by the
ring homomorphism rescaling `X` to `-X`; it includes `k>m`, where the
binomial coefficient is zero. The difference-matrix formula at line 127
therefore has the correct column-minus-row sign and bandwidth.

Edge checks made algebraically: for `m=1`, the upper binomial entries
are all one and the difference matrix has diagonal one and first
superdiagonal minus one; for `n=1`, both matrices are `[1]`; `n=0` is
valid entrywise. These are semantic checks, not additional executed
Lean or numerical tests.

No material issue was found. Replacing the raw matrix lambda with
`Matrix.of`, or narrowing the broad tactic import, would be optional
style/import cleanup. No new infrastructure is duplicating a needed
analytic power-series argument: the proof deliberately reuses the
library's formal-series unit and coefficient APIs. The weighted diagonal
factors, their relationship to the actual Toeplitz matrix, inverse
entries, and convergence in manuscript (26) are outside this theorem's
scope and remain separate obligations.
