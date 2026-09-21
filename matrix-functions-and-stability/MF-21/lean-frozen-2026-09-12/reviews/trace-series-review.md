# Independent review of the actual shifted trace series

Verdict: **APPROVE**, for the four modules and exact series-irrationality
statement below. This does not certify a finite Toeplitz trace limit or
the complete MF-21 target.

Reviewer: `/root/mf21_restart_lean_audit`, 20 September 2026. I did not
author or edit these modules. I read their complete proof bodies, the
locked statements, manuscript equations (31)–(33), the cited pinned
Mathlib APIs, and the local logs. I launched no Lean compiler. The pinned
referee standards are
`/Users/georgestepaniants/Research/project/lean-verification/REFEREE_STANDARDS.md`,
SHA-256 `e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Exact sources

Paths are relative to `MF21-restart`.

| Path | SHA-256 |
| --- | --- |
| `MF21Restart/TraceSeriesZeta.lean` | `ede5125a90d55f70cf12e2875845f36933d476923e4bacad72e93d1ca7f3dc63` |
| `MF21Restart/TraceSeriesOdd.lean` | `2b9eb28b06e83d5f3ffac358627d11737e328092b7fdce46f3d43bee27f9eda3` |
| `MF21Restart/TraceSeriesHalf.lean` | `6f35f3672cf61331220adc07b1ec9c998a62fb447b61657cf5856a8f1d516d7e` |
| `MF21Restart/TraceSeries.lean` | `7c1b2aaf0fddd59cacf63e058cc226917dd6a12207402e6e6373e1bed4ba8a59` |
| `TRACE_SERIES_STATEMENTS.md` | `bc67efd8aef474b855071608702b1ea83b94bad3a7fe4ee08a6b430bb1584ac5` |
| `MF21Restart/TraceIrrationality.lean` | `886aa32e8f60a28e4ec339d616d17e67e6f1241b99ba51020ad1e48815cd73d9` |
| `MF21Restart/PiTranscendence.lean` | `63978695081b2c4e863609090b0ae358470ae7e64e17893385237339d8315cc9` |
| `original-proof/solution.md` | `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa` |

`TraceIrrationality` and the external π proof/port were independently
reviewed earlier in `reviews/kernel-trace-pi-review.md`; these exact
dependency bytes remain unchanged. The new modules do not introduce a
transcendence assumption.

## Exact target and manuscript fidelity

`TraceSeries.lean:34–37` proves, with only `m : ℕ` and `3 <= m`,

```lean
Irrational ((Real.pi ^ (2 * m))⁻¹ *
  ∑' j : ℕ,
    (((j : ℝ) + 1 + ((m - 1 : ℕ) : ℝ) / 2) ^ (2 * m))⁻¹)
```

This is exactly manuscript (31), `solution.md:351–363`: the Lean index
`j=0` represents the published index 1, and the shift is the **real**
quotient of `m-1` by 2. Natural subtraction is harmless under `m>=3`.
There is no natural-number division rounding the even-order half shift.
The exponent `2*m` and the exterior factor `π^(-2*m)` are both retained.
Neither summability, an evaluated series value, a rational-minus
representation, nor irrationality appears among the theorem's premises.

## Zeta normalization and integer tails

1. `TraceSeriesZeta.lean:18–20` defines an explicit rational Euler
   coefficient, including the sign, `2^(2*m-1)`, Bernoulli number, and
   factorial. Lines 26–38 derive the actual real `HasSum` statement from
   pinned Mathlib `hasSum_zeta_nat` with the required `m != 0` proved
   from `1 <= m`; the casts and factor rearrangement are algebraic.
   Mathlib's theorem at `NumberTheory/ZetaValues.lean:430–446` uses exactly
   the same coefficient and the natural-index series including zero.

2. Lines 40–47 remove only the initial term at `n=0`. Its value is
   proved to be zero using `2*m != 0`, `zero_pow`, and `inv_zero`.
   This is not an application at exponent zero, where the term would
   instead equal 1. The resulting `j+1` series begins at the first
   positive integer.

3. Lines 23–24 and 49–65 define and cast the finite subtraction over
   `j=0,...,r-1`, whose denominators are `1,...,r`. The proved tail
   `HasSum` begins at `r+1`, matching equation (32). The pinned
   `hasSum_nat_add_iff'` API is the additive declaration generated from
   `Topology/Algebra/InfiniteSum/NatInt.lean:228–230`; its finite
   correction is subtracted from the original sum with the correct sign.

4. Lines 67–73 prove correction positivity from positivity of every
   term and nonemptiness of `range r` when `r>=1`. No positivity of a
   potentially alternating Bernoulli expression is assumed or needed.

5. `TraceSeriesOdd.lean:15–30` rewrites `tsum` using the proved `HasSum`
   before dividing by `π^(2*m)`. The denominator is proved nonzero.
   The value becomes the explicit rational number minus the proved
   positive rational correction divided by `π^(2*m)`, and the earlier
   arithmetic irrationality theorem then applies. Lines 38–45 set
   `m=2*r+1`, derive `r>=1` from `m>=3`, and prove `(m-1)/2=r` in ℝ.
   Thus the first valid odd case `m=3` subtracts exactly the term 1.

## Half-integer tails and even-order indexing

1. `TraceSeriesHalf.lean:31–42` proves the sum of the even-indexed
   subsequence to be `ζ(2*m)/2^(2*m)`, and derives summability of the
   odd-indexed subsequence by the proved injection `j -> 2*j+1`.
   All terms, including the zero term of the even subsequence, have
   the same positive exponent as the full zeta series.

2. Lines 43–50 use `HasSum.even_add_odd` and uniqueness of the actual
   full zeta sum. The odd-index sum is therefore
   `(1-2^(-2*m))*ζ(2*m)`. This is a justified partition of a summable
   series, rather than subtraction of unproved or divergent `tsum`
   expressions. The pinned partition API is generated from
   `NatInt.lean:77–82` and covers all natural numbers exactly once.

3. The algebraic identity at lines 21–24 gives
   `(j+1/2)^(-p) = 2^p*(2*j+1)^(-p)`. Lines 51–58 multiply the odd sum
   by the full factor `2^(2*m)`, producing `(2^(2*m)-1)*ζ(2*m)`.
   The nonzero power of 2 is explicitly supplied for cancellation.
   There is no missing factor of 2 or mistaken exponent `m` here.

4. Lines 17–19 retain that same factor in the rational correction.
   Lines 60–68 prove that its real cast is precisely
   `sum_{j=0}^{r-1} (j+1/2)^(-2*m)`. The shift theorem at lines 71–79
   then starts the tail at `r+1/2`, exactly as in equation (33).
   Lines 81–88 prove that this correction is strictly positive for
   every `r>=1`; it cannot collapse to a zero coefficient.

5. `TraceSeries.lean:15–31` applies the same justified normalization
   and irrationality argument to this half-integer tail. In its final
   parity split, lines 39–47 write `m=2*r` and prove
   `1+(2*r-1)/2 = r+1/2` as a real identity. The cast of natural
   subtraction is controlled by `(2*r-1)+1=2*r`, justified by the
   lower bound. For an even `m>=3`, necessarily `m>=4` and `r>=2`;
   the proof only needs the weaker derived `r>=1` for positivity.
   It neither drops the leading `+1` nor uses the integer-case shift.

The final parity split exhausts every `m>=3`, not a finite collection
of tested orders. The rational correction is fully specified and proved
positive before π transcendence is used.

## Supplementary exact arithmetic checks

I ran Python 3 `fractions.Fraction` calculations for the first two odd
and first two even admissible cases. These are indexing and normalization
checks, not premises of the Lean proof and not a numerical proof of
irrationality. In the form `u-v/π^(2*m)`, the independently calculated
values were:

| `m` | `r` | First series denominator | Rational `u` | Positive rational `v` |
| --- | --- | --- | --- | --- |
| 3 | 1 | 2 | `1/945` | `1` |
| 4 | 2 | `5/2` | `17/630` | `1679872/6561` |
| 5 | 2 | 3 | `1/93555` | `1025/1024` |
| 6 | 3 | `7/2` | `691/155925` | `531442002176782336/129746337890625` |

The calculation compared the first four terms of the original shifted
series to the relevant parity formula using exact fractions. For both
even cases it also checked equality of the entire finite correction in
the half-integer and scaled odd-denominator forms. All checks passed.
The following core calculation records the exact procedure:

```python
from fractions import Fraction as F
from math import factorial
B = {6: F(1, 42), 8: F(-1, 30), 10: F(5, 66), 12: F(-691, 2730)}
for m in (3, 4, 5, 6):
    p = 2*m
    r = (m-1)//2 if m % 2 else m//2
    e = F((-1)**(m+1)*2**(p-1), factorial(p))*B[p]
    shift = 1 + F(m-1, 2)
    if m % 2:
        v = sum((F(j+1)**(-p) for j in range(r)), F(0))
        u, first = e, F(1+r)
    else:
        v = F(2)**p * sum(((2*F(j)+1)**(-p) for j in range(r)), F(0))
        assert v == sum(((F(j)+F(1, 2))**(-p) for j in range(r)), F(0))
        u, first = (2**p-1)*e, F(r)+F(1, 2)
    assert first == shift and v > 0
    for j in range(4):
        assert (F(j)+shift)**(-p) == (F(j)+first)**(-p)
    print(m, r, first, u, v)
```

## Trust and execution evidence

| Inspected local log | SHA-256 | Standard-only axiom reports |
| --- | --- | --- |
| `evidence/logs/trace-series-zeta-02.log` | `59a4fc05e4ef35ba3c02a339a30139f67e734f4a123cd8b4fde549fc66f36699` | 4 |
| `evidence/logs/trace-series-odd-01.log` | `70419f2684f400f3decc870f87f08f31a30614b3f9c5e5e4a81ff6328da05dde` | 2 |
| `evidence/logs/trace-series-half-02.log` | `68b6162c0e77ac3f40a5f131ac7425ad8143eb91b89bea7824b269635c015f91` | 3 |
| `evidence/logs/trace-series-01.log` | `c711e0895f2c7e296edc990607b26b46ffccc82e27c957e07e2e59f095175d95` | 2 |

Every displayed theorem depends on exactly `propext`, `Classical.choice`,
and `Quot.sound`. The coordinator reports that these actual serial local
runs exited 0; this reviewer independently read their logs and hashed the
current source files but ran no compiler. The only warnings are an
unnecessary sequencing combinator in the integer-tail proof and an unused
`ring` after `field_simp` in the half-integer proof. They are not proof
holes or statement changes. Static inspection found no `sorry`, `admit`,
custom axiom, `unsafe`, `native_decide`, or legacy/Challenge import in the
four modules.

The pinned Mathlib source read for Euler's value has SHA-256
`491a1fc741734e2eb5a79684542bc0b57bc6333e0dc7619c47fecbaa366d8b73`
(`Mathlib/NumberTheory/ZetaValues.lean`); the shift/partition source has
SHA-256 `baf24e8f1910d71dc46896e12aeb8b0eab33bcfddd67c12c102faeb6b17f28db`
(`Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean`). These are sources in
the existing pinned Mathlib package, not newly fetched dependencies.

This closes the arithmetic irrationality assertion for the **actual**
series in (31). It does not prove (31)'s equality with a scaled inverse
Toeplitz trace limit, the majorant required for dominated convergence,
the inverse-kernel limit, or the conditional fixed-index limits needed
for the final contradiction. No unrun Comparator check, completed
original target, or increased completed-problem count is claimed.
