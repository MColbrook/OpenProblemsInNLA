import MF21Restart.ImplicitTaylor
import MF21Restart.VerticalPowerFactor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
The actual coefficient vanishing estimate (24). Differentiation of the
literal power `(2*sin(Y/2))^(2*m)` supplies the required factor; it is
not assumed as an estimate on an unspecified coefficient family.
See `COEFFICIENT_VANISHING_STATEMENTS.md`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

/-- Any jointly analytic phase with the actual initial value has the
claimed bounds for its exact derivative/factorial coefficients. -/
theorem implicitPhaseCoefficient_vanishing
    (m : ℕ) (Y : ℝ × ℝ → ℝ) (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε)
    (hY : ∀ p ∈ Set.Ioo (-r / 2) (Real.pi + r / 2) ×ˢ Set.Ioo (-ε) ε,
      ContDiffAt ℝ ⊤ Y p)
    (hYzero : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, Y (x, 0) = x) :
    ∀ k : ℕ, k ≤ 2 * m → ∃ Ck : ℝ, 0 < Ck ∧
      ∀ x ∈ Set.Icc (0 : ℝ) Real.pi,
        |implicitPhaseCoefficient m Y k x| ≤ Ck * x ^ (2 * m - k) := by
  let u : ℝ × ℝ → ℝ := fun p => 2 * Real.sin (Y p / 2)
  have hu (p : ℝ × ℝ)
      (hp : p ∈ Set.Ioo (-r / 2) (Real.pi + r / 2) ×ˢ Set.Ioo (-ε) ε) :
      ContDiffAt ℝ ⊤ u p := by
    exact contDiffAt_const.mul
      (Real.contDiff_sin.contDiffAt.comp p ((hY p hp).div_const 2))
  have hmem (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) Real.pi) :
      (x, 0) ∈ Set.Ioo (-r / 2) (Real.pi + r / 2) ×ˢ Set.Ioo (-ε) ε := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith [hx.1, hx.2]
  intro k hk
  have hc : ContinuousOn (fun x : ℝ => verticalPowerFactor u (2 * m) k (x, 0))
      (Set.Icc (0 : ℝ) Real.pi) := by
    intro x hx
    have ha := (verticalPowerFactor_contDiffAt u (2 * m) k (x, 0) (hu (x, 0) (hmem x hx))).comp x
      (contDiffAt_id.prodMk contDiffAt_const)
    exact ha.continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) Real.pi)).exists_bound_of_continuousOn hc
  have hfact : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  let Ck : ℝ := max M 1 / (k.factorial : ℝ)
  have hCk : 0 < Ck := div_pos (lt_of_lt_of_le zero_lt_one (le_max_right M 1)) hfact
  refine ⟨Ck, hCk, ?_⟩
  intro x hx
  have hufact : verticalIteratedDeriv (fun p => u p ^ (2 * m)) k (x, 0) =
      u (x, 0) ^ (2 * m - k) * verticalPowerFactor u (2 * m) k (x, 0) :=
    verticalIteratedDeriv_pow_factor u (2 * m) k (x, 0) (hu (x, 0) (hmem x hx)) hk
  have hcoeff : implicitPhaseCoefficient m Y k x =
      (u (x, 0) ^ (2 * m - k) * verticalPowerFactor u (2 * m) k (x, 0)) /
        (k.factorial : ℝ) := by
    change verticalIteratedDeriv (fun p => u p ^ (2 * m)) k (x, 0) /
      (k.factorial : ℝ) = _
    rw [hufact]
  have huvalue : u (x, 0) = 2 * Real.sin (x / 2) := by
    dsimp only [u]
    rw [hYzero x hx]
  have hubound : |u (x, 0)| ≤ x := by
    rw [huvalue, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    calc
      2 * |Real.sin (x / 2)| ≤ 2 * |x / 2| :=
        mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
      _ = x := by rw [abs_of_nonneg (by linarith [hx.1] : 0 ≤ x / 2)]; ring
  have hAbound : |verticalPowerFactor u (2 * m) k (x, 0)| ≤ max M 1 := by
    have hb : |verticalPowerFactor u (2 * m) k (x, 0)| ≤ M := by
      simpa only [Real.norm_eq_abs] using hM x hx
    exact hb.trans (le_max_left M 1)
  have hpow : |u (x, 0)| ^ (2 * m - k) ≤ x ^ (2 * m - k) :=
    pow_le_pow_left₀ (abs_nonneg _) hubound _
  rw [hcoeff, abs_div, abs_mul, abs_pow, abs_of_pos hfact]
  calc
    _ ≤ (x ^ (2 * m - k) * max M 1) / (k.factorial : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul hpow hAbound (abs_nonneg _) (pow_nonneg hx.1 _)) hfact.le
    _ = Ck * x ^ (2 * m - k) := by dsimp only [Ck]; ring

/-- The same actual implicit phase and exact coefficient family satisfy
both the uniform all-order Taylor formula and the vanishing bounds. -/
theorem manuscript_uniform_implicit_taylor_with_vanishing (m : ℕ) (hm : 1 ≤ m) :
    ∃ r ε C δ : ℝ, 0 < r ∧ 0 < ε ∧ 0 < C ∧ 0 < δ ∧ δ < ε ∧
      ∃ Y : ℝ × ℝ → ℝ,
      let D := Set.Ioo (-r / 2) (Real.pi + r / 2) ×ˢ Set.Ioo (-ε) ε
      (∀ p ∈ D, ContDiffAt ℝ ⊤ Y p) ∧
      (∀ p ∈ D, Y p ∈ Set.Ioo (-r) (Real.pi + r) ∧
        Y p = p.1 + p.2 * manuscriptEta m (Y p) ∧
        |Y p - p.1| ≤ C * |p.2|) ∧
      (∀ x ∈ Set.Ioo (-r / 2) (Real.pi + r / 2), Y (x, 0) = x) ∧
      (∀ p ∈ D, ∀ y ∈ Set.Icc (-r) (Real.pi + r),
        y = p.1 + p.2 * manuscriptEta m y → y = Y p) ∧
      (∀ k : ℕ, ∀ x ∈ Set.Ioo (-r / 2) (Real.pi + r / 2),
        ContDiffAt ℝ ⊤ (implicitPhaseCoefficient m Y k) x) ∧
      (∀ x ∈ Set.Ioo (-r / 2) (Real.pi + r / 2),
        implicitPhaseCoefficient m Y 0 x = symbol m x) ∧
      (∀ p : ℕ, ∃ Cp : ℝ, 0 < Cp ∧
        ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, ∀ h : ℝ, |h| ≤ δ →
          |symbol m (Y (x, h)) -
              ∑ k ∈ Finset.range (p + 1), implicitPhaseCoefficient m Y k x * h ^ k| ≤
            Cp * |h| ^ (p + 1)) ∧
      (∀ k : ℕ, k ≤ 2 * m → ∃ Ck : ℝ, 0 < Ck ∧
        ∀ x ∈ Set.Icc (0 : ℝ) Real.pi,
          |implicitPhaseCoefficient m Y k x| ≤ Ck * x ^ (2 * m - k)) := by
  obtain ⟨r, ε, C, δ, hr, hε, hC, hδ, hδε, Y,
    hYreg, hYeq, hYzero, hYuniq, hcoeff, hzeroCoeff, hrem⟩ :=
    manuscript_uniform_implicit_taylor m hm
  refine ⟨r, ε, C, δ, hr, hε, hC, hδ, hδε, Y,
    hYreg, hYeq, hYzero, hYuniq, hcoeff, hzeroCoeff, hrem, ?_⟩
  apply implicitPhaseCoefficient_vanishing m Y r ε hr hε hYreg
  intro x hx
  apply hYzero x
  constructor <;> linarith [hx.1, hx.2]

#print axioms implicitPhaseCoefficient_vanishing
#print axioms manuscript_uniform_implicit_taylor_with_vanishing

end MF21Restart
