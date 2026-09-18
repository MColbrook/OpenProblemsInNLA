# MI-28 current numerical certificate

The only numerical target is frozen contract C01:

```lean
theorem half_exponent_interval : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1
```

`NLA/MI28/Numerical.lean` proves both fixed scalar inequalities with
`interval_decide (trust := kernel)` and sets `leancert.trust` to `kernel`.
There is no matrix-entry grid, real-parameter grid, numerical spectral
approximation, conjectural bound or native proof oracle. Natural-number
induction in the Furuta extension is a symbolic proof of an unbounded result,
not a finite parameter check.

The lower bound is mathematically consumed: C02's modulus-square proof supplies
`half_exponent_interval.1.le` to the nonnegative-exponent hypothesis of
`CFC.rpow_rpow_of_exponent_nonneg`. This composes the half power and the square
of the genuine Gram matrix, proving `|AB|² = B A² B`. The upper-half inequality
is co-certified in the frozen conjunction; no separate mathematical necessity
for that second inequality is claimed.

Root's actual local356 compilation first checked this source; local365's
complete proof closure authenticates the exact successful output and all 20
aggregate `#assert_trust kernel` checks. Local366's actual elaborated proof-body
graph records the route:

```text
determinant_comparison → full_log_majorization
  → normalized_determinants_eq → det_product_modulus_re
  → product_modulus_square → half_exponent_interval
```

It also reaches the generated closed certificate constants
`half_exponent_interval._proof_1_7` and `_proof_1_15`, each reaching
`LeanCert.Validity.checkStrictUpperBoundDyadicChecked`, and the validity theorem
`LeanCert.Validity.verify_strict_upper_bound_dyadic_checked`. The two strict
inequalities are encoded using this same strict-upper-bound checking interface;
the record does not claim a separate strict-lower-bound verifier.

The exact source hash is in [IMPLEMENTATION-MAP.json](IMPLEMENTATION-MAP.json).
The complete local record has SHA-256
`94a60f882bd02a9333db7e92a15b7045404b8ed43222dab744610abe60e01f39`;
the type/body diagnostic record has SHA-256
`54cbbfe2497939fe78fbff9dd499b99c961316f6a22e36a98ba0fa7cc0256d45`.
The certificate is proved internally from pinned LeanCert and standard axioms;
no literature theorem is imported as an axiom. The CFC/domain argument reuses
the credited MI24 proof pattern and the numerical setup reuses the MF05 idiom.

This is the current execution description. The earlier unimplemented numerical
plan remains unchanged in `history/statement-draft/NUMERICAL_TARGETS.md`.
Reading or authenticating these receipts does not rerun Lean. The later actual Linux run 35374928604 passed Comparator/default-kernel/sandbox checks at immutable proof commit `aae2941f9a7f1e28b8010f5216574d93bdc72181`. Its [retained evidence](verification/linux-2026-09-18/README.md) is distinct from local diagnostics and source review.
