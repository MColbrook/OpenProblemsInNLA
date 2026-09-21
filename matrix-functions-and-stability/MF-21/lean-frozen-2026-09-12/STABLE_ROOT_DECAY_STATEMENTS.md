# Stable root decay: statement first

This lock precedes `MF21Restart/StableRootDecay.lean`. It addresses the
compactness step in manuscript (6) for the actual quadratic-formula branch,
with one fixed parameter `κ` satisfying `0 < κ.re`. It does not assume an
exponential estimate, an extended-slope sign, or a positive uniform gap.

The scalar lemma uses only continuity on a compact interval, the actual
derivative at zero, and strict decrease below the endpoint value at every
positive argument. Extend `(f(x)-1)/x` at zero by the derivative. Its
continuity and strict negativity give a negative attained maximum. This
first gives a linear bound and then the exponential bound through
`1 + y ≤ exp y`. No logarithms, numerical certificates, or extra axioms are
needed.

The exact public statements are:

```lean
theorem exists_pos_linear_upper_bound_of_neg_deriv
    (f : ℝ → ℝ) (L d : ℝ) (hL : 0 < L)
    (hf : ContinuousOn f (Set.Icc 0 L)) (hf0 : f 0 = 1)
    (hd : HasDerivAt f d 0) (hdneg : d < 0)
    (hlt : ∀ x : ℝ, 0 < x → x ≤ L → f x < 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ x : ℝ, 0 ≤ x → x ≤ L → f x ≤ 1 - c * x

theorem exists_pos_exp_upper_bound_of_neg_deriv
    (f : ℝ → ℝ) (L d : ℝ) (hL : 0 < L)
    (hf : ContinuousOn f (Set.Icc 0 L)) (hf0 : f 0 = 1)
    (hd : HasDerivAt f d 0) (hdneg : d < 0)
    (hlt : ∀ x : ℝ, 0 < x → x ≤ L → f x < 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ x : ℝ, 0 ≤ x → x ≤ L → f x ≤ Real.exp (-c * x)

theorem stableRootCurve_norm_hasDerivAt_zero (κ : ℂ) :
    HasDerivAt (fun θ : ℝ => ‖stableRootCurve κ θ‖) (-κ.re) 0

theorem stableRootCurve_exp_decay (κ : ℂ) (hκ : 0 < κ.re) :
    ∃ c : ℝ, 0 < c ∧ ∀ θ : ℝ, 0 ≤ θ → θ ≤ Real.pi →
      ‖stableRootCurve κ θ‖ ≤ Real.exp (-c * θ)
```

The norm derivative is derived from `stableRootCurve κ 0 = 1` and the
already proved complex-valued derivative `-κ`, by differentiating the
squared norm and taking its positive square root. It is valid for every
`κ`; positivity of `κ.re` enters only when obtaining decay. The actual
curve's continuity and strict norm bound come from `StableRootSmooth`.

The constant may depend on `κ`. Taking the minimum over the finitely many
published indices `1 ≤ ell < m`, and obtaining bounds for powers of the
roots, remain separate steps. This ingredient alone is not a completed
MF-21 target or the entire determinant remainder estimate.

Validation policy: this author does not run Lean; the coordinator performs
the serial local compile. A statement lock and a source review are not
claims of a successful local compile or a GitHub Comparator run.
