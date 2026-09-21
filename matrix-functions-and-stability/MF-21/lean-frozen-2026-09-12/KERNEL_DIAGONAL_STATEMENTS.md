# Diagonal kernel substitution

Statement lock for `MF21Restart/KernelDiagonal.lean`, 20 September 2026.
These statements are recorded before writing the proof module.

The first obligation evaluates the exact scalar change of variables used
between manuscript (27) and (28). For a natural exponent k and 0 < x ≤ 1:

    theorem kernel_diagonal_substitution (k : ℕ) (x : ℝ)
        (hx : 0 < x) (hx1 : x ≤ 1) :
        (∫ t in x..1, (t - x) ^ k / t ^ (k + 2)) =
          (1 - x) ^ (k + 1) / (((k + 1 : ℕ) : ℝ) * x)

The proof must derive this integral using u = 1 - x/t, its actual
derivative x/t², and Mathlib's interval-integral substitution theorem.
No integral identity or Green-kernel diagonal formula may be assumed.
The lower endpoint is positive so the derivative and integrand denominators
are nonzero throughout [x,1]; the degenerate interval x=1 is included.

The second obligation specializes k=2m-2 and retains the literal two
factors from (27) at y=x, including the factorial normalization:

    theorem kernel_diagonal_integral_value (m : ℕ) (hm : 1 ≤ m)
        (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
        (x ^ m * x ^ m / ((m - 1).factorial : ℝ) ^ 2) *
          (∫ t in x..1,
            ((t - x) ^ (m - 1) * (t - x) ^ (m - 1)) / t ^ (2 * m)) =
        x ^ (2 * m - 1) * (1 - x) ^ (2 * m - 1) /
          (((2 * m - 1 : ℕ) : ℝ) * ((m - 1).factorial : ℝ) ^ 2)

At y=x the lower bound max(x,y) equals x. The scalar integral identity is
valid for every positive x≤1. In the manuscript, (27) is applied directly
only for x≥1/2, and a separately justified reflection of the actual kernel
then extends the diagonal formula to [0,1]. This module proves no Green
kernel representation, reflection theorem, inverse-kernel convergence,
Toeplitz trace limit, or MF-21 Target. In particular it does not use the
singular substitution at x=0 or assume that (27) defines the kernel on its
entire square. Those links remain distinct obligations.

This is a symbolic analytic calculation with no numerical certification.
The authoring agent must not run Lean; the coordinator supplies the actual
serial local compile and axiom audit. Any later Comparator run is separate.
