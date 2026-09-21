# Diagonal trace integral: statement selected before proof

This file records the exact statements before TraceIntegral.lean is written.
The source is manuscript equations (28)–(29), with the manuscript unchanged.
The extension to m>=1 is valid and contains the requested m>=3 cases.

The first target is the concrete interval-integral identity:

    theorem diagonal_kernel_integral_value (m : ℕ) (hm : 1 ≤ m) :
        (∫ x in (0 : ℝ)..1,
          x ^ (2 * m - 1) * (1 - x) ^ (2 * m - 1) /
            (((2 * m - 1 : ℕ) : ℝ) * ((m - 1).factorial : ℝ) ^ 2)) =
        ((2 * m - 1).factorial : ℝ) ^ 2 /
          (((4 * m - 1).factorial : ℝ) *
            ((2 * m - 1 : ℕ) : ℝ) * ((m - 1).factorial : ℝ) ^ 2)

The two additional targets concern this same integral:

    theorem diagonal_kernel_integral_pos (m : ℕ) (hm : 1 ≤ m) :
        0 < (∫ x in (0 : ℝ)..1,
          x ^ (2 * m - 1) * (1 - x) ^ (2 * m - 1) /
            (((2 * m - 1 : ℕ) : ℝ) * ((m - 1).factorial : ℝ) ^ 2))

    theorem diagonal_kernel_integral_rational (m : ℕ) (hm : 1 ≤ m) :
        ∃ q : ℚ, (∫ x in (0 : ℝ)..1,
          x ^ (2 * m - 1) * (1 - x) ^ (2 * m - 1) /
            (((2 * m - 1 : ℕ) : ℝ) * ((m - 1).factorial : ℝ) ^ 2)) = (q : ℝ)

Planned reuse is the pinned Mathlib Beta/Gamma identity and Gamma's
factorial evaluation at positive integer arguments. A small general
polynomial-integral lemma will specialize that proved identity:

    theorem integral_pow_mul_one_sub_pow (p q : ℕ) :
        (∫ x in (0 : ℝ)..1, x ^ p * (1 - x) ^ q) =
          (p.factorial : ℝ) * (q.factorial : ℝ) /
            ((p + q + 1).factorial : ℝ)

No conclusion above is an assumption. Positivity will follow from positive
factorials and 2m-1>0; rationality will use the explicit same quotient in ℚ.
No numerical enumeration or certificate is needed.

This supplies only the integral evaluation once the diagonal kernel formula
(28) is known. It does not prove the inverse-kernel convergence, the passage
from finite matrix traces to an integral, or the diagonal substitution from
(27) to (28). Those remain separate obligations. Any substitution guidance
will be recorded separately after this bounded task.

The agent will not launch a Lean compiler. The new module will be sent to
the coordinator for serialized local testing with one thread and a
4096 MiB limit. This statement lock makes no compilation claim.
