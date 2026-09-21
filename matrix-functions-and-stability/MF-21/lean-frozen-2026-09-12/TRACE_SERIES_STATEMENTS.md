# Trace-series arithmetic: statements before proof

Frozen manuscript Section 5, equations (32)–(33), 20 September 2026.
The target is the actual shifted series from (31):

    theorem trace_series_irrational (m : ℕ) (hm : 3 ≤ m) :
      Irrational ((Real.pi ^ (2 * m))⁻¹ *
        ∑' j : ℕ,
          (((j : ℝ) + 1 + ((m - 1 : ℕ) : ℝ) / 2) ^ (2 * m))⁻¹)

The natural index j starts at zero; j+1 is the published index starting
at one. The shift is the real quotient of the natural number m-1 by 2,
not natural-number division. All displayed powers have natural exponent
2*m and the inverse is the ordinary real field inverse.

No rational-minus form, tail identity, summability, Euler evaluation, or
irrationality may be assumed. Derive Euler's value using the pinned
Mathlib theorem `hasSum_zeta_nat`; use proved HasSum shift and even/odd
partition APIs for the tails. The arithmetic irrationality lemma from
`TraceIrrationality.lean` may be reused only after deriving the form and
strict positivity of the finite rational correction.

The new proof modules may expose these explicit rational definitions:

    def evenZetaRational (m : ℕ) : ℚ :=
      (-1 : ℚ) ^ (m + 1) * (2 : ℚ) ^ (2 * m - 1) *
        bernoulli (2 * m) / ((2 * m).factorial : ℚ)

    def integerTailCorrection (m r : ℕ) : ℚ :=
      ∑ j ∈ Finset.range r, (((j : ℚ) + 1) ^ (2 * m))⁻¹

    def halfIntegerTailCorrection (m r : ℕ) : ℚ :=
      (2 : ℚ) ^ (2 * m) *
        ∑ j ∈ Finset.range r, ((2 * (j : ℚ) + 1) ^ (2 * m))⁻¹

`TraceSeriesZeta.lean` first proves, for 1≤m, the following HasSum results:

* n↦((n:ℝ)^(2*m))⁻¹ sums to
  `(evenZetaRational m : ℝ) * Real.pi^(2*m)`.
* j↦(((j:ℝ)+1)^(2*m))⁻¹ has that same sum; the zero-index term of the
  preceding series is proved zero, since 2*m>0.
* j↦(((j:ℝ)+1+(r:ℝ))^(2*m))⁻¹ sums to that value minus
  `(integerTailCorrection m r : ℝ)` for every natural r.
* `0 < integerTailCorrection m r` for 1≤r (all natural m).

`TraceSeriesOdd.lean` may first deliver the exact odd case as a bounded
partial result:

    theorem trace_series_irrational_of_odd (m : ℕ)
        (hm : 3 ≤ m) (hodd : Odd m) :
      Irrational ((Real.pi ^ (2 * m))⁻¹ *
        ∑' j : ℕ,
          (((j : ℝ) + 1 + ((m - 1 : ℕ) : ℝ) / 2) ^ (2 * m))⁻¹)

For m=2r+1 this must derive (32) using the positive finite correction
over 1,...,r. An auxiliary theorem may use independent parameters m≥1
and r≥1 for the corresponding normalized integer-shift series.

`TraceSeriesHalf.lean` then proves the half-integer tail HasSum formula
for m≥1 and any r:

    HasSum (fun j : ℕ => (((j : ℝ) + (r : ℝ) + 1/2) ^ (2*m))⁻¹)
      (((((2 : ℚ) ^ (2*m) - 1) * evenZetaRational m : ℚ) : ℝ) *
          Real.pi ^ (2*m) - (halfIntegerTailCorrection m r : ℝ))

The factor 2^(2m)-1 is derived by even/odd partition of the integer
zeta series, and the correction is proved strictly positive for r≥1.
This is exactly (33), with m=2r; no odd denominator or power-of-two
normalization may be dropped. `TraceSeries.lean` combines the two parity
cases to prove the full displayed target with hm≥3.

These series facts do not identify a finite Toeplitz trace limit, prove
dominated convergence for eigenvalue reciprocals, or prove MF-21 Target.
The original manuscript and shared Definitions remain unchanged. The
authoring agent runs no compiler; local serial tests and any eventual
Comparator run are recorded separately.
