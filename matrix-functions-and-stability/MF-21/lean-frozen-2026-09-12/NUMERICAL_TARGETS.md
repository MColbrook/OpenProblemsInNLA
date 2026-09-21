# Numerical certification scope

The numerical statement was selected in STATEMENTS.md before Numerics.lean
was written. This file collects that already locked scope for reproduction.

The sole numerical residual is the closed inequality `1 ≤ Real.sqrt 2`.
Numerics.lean sets `leancert.trust` to `"kernel"` and uses
`leancert_verify_cert` to check the exact rational lower certificate
`sqrtRatLowerPrec (2 : ℚ) 0 = 1`. LeanCert's proved
`sqrtRatLowerPrec_le_sqrt` theorem transports this certificate to the real
inequality. Scale zero reduces the certificate computation to `Nat.sqrt 2`;
there is no adaptive interval evaluation. The statement and implementation
plan were fixed in
[NUMERICS_MINIMAL_CERTIFICATE_STATEMENTS.md](NUMERICS_MINIMAL_CERTIFICATE_STATEMENTS.md)
before this replacement was written. Mathlib's exact identity
`sin(pi/4) = sqrt(2)/2` and linear arithmetic then prove the strict margin
`1/4 < sin(pi/4)` used by the phase-window argument.

There is no variable interval to subdivide, numerical eigenvalue computation,
matrix-size enumeration, numerical integration, or externally asserted
certificate. All parameter-dependent estimates in the proof are symbolic.
The certificate is proved once and reused, and `#assert_trust kernel`
checks the complete margin theorem. The transitive axiom reports
for the margin and complete target permit only `propext`, `Classical.choice`,
and `Quot.sound`.

Actual local execution evidence is in VERIFICATION.md. A local LeanCert
success does not assert that GitHub Comparator or its Linux sandbox has run.
