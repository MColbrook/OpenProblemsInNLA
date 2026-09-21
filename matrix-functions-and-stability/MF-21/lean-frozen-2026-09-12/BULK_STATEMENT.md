# Logarithmic bulk scale gain: statement selected before proof

This module supplies one analytic ingredient for manuscript equation (25).
It does not prove a Toeplitz eigenvalue estimate, construct the coefficient
functions, or establish the complete MF-21 target.

The exact selected theorem is:

    theorem exists_log_sq_bulk_scale_gain
        (c : ℝ) (hc : 0 < c) (q : ℕ) :
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ,
          Nat.ceil ((Real.log (n + 2 : ℝ)) ^ 2) ≤ j →
          (n + 2 : ℝ) * (j : ℝ) ^ q *
            Real.exp (-c * (j : ℝ)) ≤ 1

The theorem is uniform over every natural j above the stated threshold.
No upper bound j≤n is required. The eventual cutoff N may depend on c and q.
There are no assumed remainder estimates or unproved asymptotic premises.

For the manuscript, take q=2m−1. Multiplying its spectral approximation
bound A*h^(2m)*j^(2m−1)*exp(−c*j) by this estimate yields
A*h^(2m+1) in the logarithmic bulk. The Taylor remainder is controlled
separately and has no exponential factor.

The proof splits exp(−c*j) into two factors of rate c/2. Mathlib's
polynomial-times-exponential limit absorbs j^q in the first. Once
log(n+2)≥2/c, the condition j≥log(n+2)^2 makes the second at most
1/(n+2). A larger logarithmic cutoff also ensures the polynomial estimate
holds for every admissible j.

Planned library reuse: the pinned Mathlib theorem
tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero, Real.tendsto_log_atTop,
Nat.le_ceil, and elementary exponential/order identities. The pinned output
for Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics is available locally.
No numerical certificate, parameter enumeration, or new proof axiom is needed.

This statement was recorded before writing BulkDecay.lean. The source will
be submitted to the coordinator for serial local compilation with one thread
and a 4096 MiB limit; this statement document does not claim a successful run.
