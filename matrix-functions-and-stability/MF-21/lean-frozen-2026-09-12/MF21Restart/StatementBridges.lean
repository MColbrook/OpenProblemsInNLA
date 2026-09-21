import MF21Restart.Definitions
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
Two source-fidelity obligations selected in STATEMENTS.md: the real cosine
coefficient represents the original complex Fourier integral, and the bulk
cutoff already forces the published positive index range.
-/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

lemma symbol_neg (m : ℕ) (θ : ℝ) : symbol m (-θ) = symbol m θ := by
  simp [symbol, neg_div, Real.sin_neg, mul_neg, pow_mul]

lemma integral_symbol_sin (m : ℕ) (k : ℤ) :
    (∫ θ in -Real.pi..Real.pi, symbol m θ * Real.sin ((k : ℝ) * θ)) = 0 := by
  have h := intervalIntegral.integral_comp_neg
    (fun θ : ℝ => symbol m θ * Real.sin ((k : ℝ) * θ))
    (a := -Real.pi) (b := Real.pi)
  have hn : -(∫ θ in -Real.pi..Real.pi,
      symbol m θ * Real.sin ((k : ℝ) * θ)) =
      ∫ θ in -Real.pi..Real.pi, symbol m θ * Real.sin ((k : ℝ) * θ) := by
    simpa only [symbol_neg, mul_neg, Real.sin_neg,
      intervalIntegral.integral_neg, neg_neg] using h
  linarith

lemma fourier_integrand (m : ℕ) (k : ℤ) (θ : ℝ) :
    (symbol m θ : ℂ) * Complex.exp (-Complex.I * (k : ℂ) * (θ : ℂ)) =
      ((symbol m θ * Real.cos ((k : ℝ) * θ) : ℝ) : ℂ) -
        ((symbol m θ * Real.sin ((k : ℝ) * θ) : ℝ) : ℂ) * Complex.I := by
  have he : -Complex.I * (k : ℂ) * (θ : ℂ) =
      ((-((k : ℝ) * θ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_mul, Complex.ofReal_neg]
  ring

/-- Literal complex Fourier coefficient from the original problem, including
its normalization, negative exponential sign, and signed integer frequency. -/
theorem complex_fourier_eq_cosine (m : ℕ) (k : ℤ) :
    (1 / (2 * (Real.pi : ℂ))) *
      (∫ θ in -Real.pi..Real.pi,
        (symbol m θ : ℂ) * Complex.exp (-Complex.I * (k : ℂ) * (θ : ℂ))) =
      (fourierCoeff m k : ℂ) := by
  have hc : IntervalIntegrable
      (fun θ : ℝ => ((symbol m θ * Real.cos ((k : ℝ) * θ) : ℝ) : ℂ))
      MeasureTheory.volume (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    unfold symbol
    fun_prop
  have hs : IntervalIntegrable
      (fun θ : ℝ => ((symbol m θ * Real.sin ((k : ℝ) * θ) : ℝ) : ℂ) * Complex.I)
      MeasureTheory.volume (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    unfold symbol
    fun_prop
  simp_rw [fourier_integrand]
  rw [intervalIntegral.integral_sub hc hs, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
    integral_symbol_sin]
  simp [fourierCoeff]

theorem bulk_cutoff_pos (n : ℕ) :
    1 ≤ Nat.ceil ((Real.log (n + 2 : ℝ)) ^ 2) := by
  have ht : 1 < (n + 2 : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hl : 0 < Real.log (n + 2 : ℝ) := Real.log_pos ht
  have hs : 0 < (Real.log (n + 2 : ℝ)) ^ 2 := pow_pos hl 2
  exact Nat.one_le_iff_ne_zero.mpr (by
    intro hz
    have hceil := Nat.le_ceil ((Real.log (n + 2 : ℝ)) ^ 2)
    rw [hz, Nat.cast_zero] at hceil
    exact (not_le_of_gt hs) hceil)

#print axioms complex_fourier_eq_cosine
#print axioms bulk_cutoff_pos

end MF21Restart
