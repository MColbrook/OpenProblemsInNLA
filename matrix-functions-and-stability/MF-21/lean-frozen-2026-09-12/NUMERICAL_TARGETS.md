# Numerical certification scope

The numerical statement was selected in STATEMENTS.md before Numerics.lean
was written. This file collects that already locked scope for reproduction.

The sole numerical residual is the closed inequality `1 ≤ Real.sqrt 2`.
Numerics.lean sets `leancert.trust` to `"kernel"` and proves it with
`interval_decide (trust := kernel)`. Mathlib's exact identity
`sin(pi/4) = sqrt(2)/2` and linear arithmetic then prove the strict margin
`1/4 < sin(pi/4)` used by the phase-window argument.

There is no variable interval to subdivide, numerical eigenvalue computation,
matrix-size enumeration, numerical integration, or externally asserted
certificate. All parameter-dependent estimates in the proof are symbolic.
The certificate is proved once and reused. The transitive axiom reports
for the margin and complete target permit only `propext`, `Classical.choice`,
and `Quot.sound`.

Actual local execution evidence is in VERIFICATION.md. A local LeanCert
success does not assert that GitHub Comparator or its Linux sandbox has run.
