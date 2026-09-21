# Full MF-21 Comparator contracts

Locked before adding the full-theorem Challenge/Solution wrappers.
The prior mathematical targets are Definitions.lean and
TARGET_ASSEMBLY_STATEMENTS.md; no mathematical target is changed here.

The shared Definitions.lean SHA256 is
`35a74047a81a9b7526e9bf039880ca8f07ae33314e2b5b960ab254e02fca4b51`.
The unchanged manuscript SHA256 is
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`.

The final configuration will retain the five existing component contracts
and add these two complete results in namespace MF21Restart.Contracts:

- `target_proved : MF21Restart.Target`, with no additional hypotheses.
- `manuscript_smooth_target`: for each integer m >= 3, one coefficient
  family d is smooth at every point of the closed interval [0, pi] for
  every order k <= 2m, d_0 is the actual symbol, and the same family
  satisfies all global orders p <= 2m-1, the exact logarithmic bulk
  cutoff at order 2m, and failure of the global critical bound.

Smoothness means ContDiffAt with order infinity, not analytic top.
The Challenge imports only the already locked definitions and Mathlib's
calculus definitions needed to state smoothness; it imports no solution
module. It contains deliberate theorem placeholders, not definition holes.
The Solution proves identically named, identically typed declarations and
does not import Challenge. Permitted axioms remain exactly propext,
Classical.choice, and Quot.sound.

Preparing or compiling these contracts is not a Comparator success.
Only an actual source-matched non-root Linux sandbox/comparison/kernel run
will be reported as such, with its published commit, logs, and run ID.
