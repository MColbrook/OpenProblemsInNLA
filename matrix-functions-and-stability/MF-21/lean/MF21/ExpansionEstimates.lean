import MF21.FiniteHeadModel
import MF21.ExponentialCutoff

/-! All expansion estimates follow from the actual eigenangle tail theorem. -/
noncomputable section
open Set Filter Finset
open scoped Topology BigOperators
namespace MF21Expansion

def UniformModelError (m : ℕ) (model : MF21Quantization.Model m) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : Fin n,
    |MF21Challenge.eigenvalue m n j - model.F (MF21Challenge.grid n j, step n)| ≤
      K * step n ^ (2 * m)

theorem uniformModelError_of_tailSymbol (m : ℕ) (hm : 1 ≤ m)
    (model : MF21Quantization.Model m) (htail : TailSymbolApproximation m model) :
    UniformModelError m model := by
  obtain ⟨J, N, B, c, hB, hc, ht⟩ := htail
  obtain ⟨K, hK, hh⟩ := finite_head_model_error m hm model J
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (step_tendsto.eventually_lt_const model.Hpos)
  let T : ℝ := B * ((2 * m - 1).factorial : ℝ) / c ^ (2 * m - 1)
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨K + T, by positivity, max N N₁, ?_⟩
  intro n hn j
  by_cases hj : J ≤ j.val + 1
  · have htailn := ht n ((le_max_left _ _).trans hn) j hj
    have hb := exponential_power_bound (2 * m - 1) c (j.val + 1 : ℕ) hc (by positivity)
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb hB.le) (pow_nonneg (step_pos n).le (2 * m))
    apply htailn.trans (hmul.trans ?_)
    calc
      _ = T * step n ^ (2 * m) := by dsimp [T]; ring
      _ ≤ (K + T) * step n ^ (2 * m) :=
        mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (step_pos n).le _)
  · exact (hh n j (by omega) (hN₁ n ((le_max_right _ _).trans hn)).le).trans
      (by nlinarith [pow_nonneg (step_pos n).le (2 * m)])

theorem step_le_one (n : ℕ) : step n ≤ 1 := by
  rw [step, inv_le_one₀ (by positivity : 0 < (n : ℝ) + 2)]
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem remainder_eq (m p n : ℕ) (model : MF21Quantization.Model m) (j : Fin n) :
    MF21Challenge.remainder m p n model.d j =
      (MF21Challenge.eigenvalue m n j - model.F (MF21Challenge.grid n j, step n)) +
      (model.F (MF21Challenge.grid n j, step n) -
        ∑ k ∈ range (p + 1), model.d k (MF21Challenge.grid n j) * step n ^ k) := by
  simp only [MF21Challenge.remainder, step, inv_pow, div_eq_mul_inv]
  ring

theorem uniformOrder_of_uniformModelError (m p : ℕ) (hp : p + 1 ≤ 2 * m)
    (model : MF21Quantization.Model m) (herr : UniformModelError m model) :
    MF21Challenge.UniformOrder m p model.d := by
  obtain ⟨K, hK, N, hN⟩ := herr
  obtain ⟨D, hD, ht⟩ := model.uniform_taylor p
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (step_tendsto.eventually_lt_const model.Hpos)
  refine ⟨K + D, by positivity, max N N₁, ?_⟩
  intro n hn j
  have he := hN n ((le_max_left _ _).trans hn) j
  have hT := ht _ (grid_mem n j) _ ⟨(step_pos n).le, (hN₁ n ((le_max_right _ _).trans hn)).le⟩
  have hpow := pow_le_pow_of_le_one (step_pos n).le (step_le_one n) hp
  rw [remainder_eq]
  apply (abs_add_le _ _).trans
  calc
    _ ≤ K * step n ^ (2 * m) + D * step n ^ (p + 1) := add_le_add he hT
    _ ≤ (K + D) * step n ^ (p + 1) := by nlinarith [mul_le_mul_of_nonneg_left hpow hK.le]
    _ = (K + D) / ((n : ℝ) + 2) ^ (p + 1) := by rw [step, inv_pow, div_eq_mul_inv]

theorem cutoff_ge_eventually (J : ℕ) : ∀ᶠ n in atTop, J ≤ MF21Challenge.cutoff n := by
  have hl := (Real.tendsto_log_atTop.comp MF21Mesh.denominator_atTop).eventually
    (eventually_ge_atTop (max 1 (J : ℝ)))
  filter_upwards [hl] with n hn
  have h1 : 1 ≤ Real.log (MF21Mesh.denominator n) := (le_max_left _ _).trans hn
  have hJ : (J : ℝ) ≤ Real.log (MF21Mesh.denominator n) := (le_max_right _ _).trans hn
  have hsq : (J : ℝ) ≤ (Real.log (MF21Mesh.denominator n)) ^ 2 := by nlinarith
  have hc := hsq.trans (Nat.le_ceil _)
  exact_mod_cast hc

theorem bulkTopOrder_of_tailSymbol (m : ℕ) (model : MF21Quantization.Model m)
    (htail : TailSymbolApproximation m model) : MF21Challenge.BulkTopOrder m model.d := by
  obtain ⟨J, N, B, c, hB, hc, ht⟩ := htail
  obtain ⟨D, hD, hT⟩ := model.uniform_taylor (2 * m)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (step_tendsto.eventually_lt_const model.Hpos)
  obtain ⟨N₂, hN₂⟩ := log_squared_exponential_cutoff (2 * m - 1) c hc
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.mp (cutoff_ge_eventually J)
  let K : ℝ := B * ((2 * m - 1).factorial : ℝ) / (c / 2) ^ (2 * m - 1)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K + D, by positivity, max (max N N₁) (max N₂ N₃), ?_⟩
  intro n hn j hj
  have hn0 : N ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hn1 : N₁ ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hn2 : N₂ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn3 : N₃ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have he := ht n hn0 j ((hN₃ n hn3).trans hj)
  have hcj := hN₂ n hn2 (j.val + 1) hj
  have hM := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcj hB.le) (pow_nonneg (step_pos n).le (2 * m))
  have he' : |MF21Challenge.eigenvalue m n j - model.F (MF21Challenge.grid n j, step n)| ≤
      K * step n ^ (2 * m + 1) := he.trans (hM.trans_eq (by
        dsimp [K, step]
        rw [pow_succ]
        simp only [div_eq_mul_inv]
        ring))
  have htj := hT _ (grid_mem n j) _ ⟨(step_pos n).le, (hN₁ n hn1).le⟩
  rw [remainder_eq]
  apply (abs_add_le _ _).trans
  calc
    _ ≤ K * step n ^ (2 * m + 1) + D * step n ^ (2 * m + 1) := add_le_add he' htj
    _ = (K + D) / ((n : ℝ) + 2) ^ (2 * m + 1) := by
      rw [step, inv_pow, div_eq_mul_inv]
      ring

/-- The first two MF-21 assertions are now conditional only on the concrete
actual-eigenangle tail theorem, using the same coefficients at every order. -/
theorem expansion_assertions_of_tailAngle (m : ℕ) (hm : 1 ≤ m)
    (model : MF21Quantization.Model m) (htail : TailAngleApproximation m model) :
    MF21Challenge.ContinuousCoefficients m model.d ∧
    (∀ x ∈ Icc 0 Real.pi, model.d 0 x = MF21Challenge.symbol m x) ∧
    (∀ p : ℕ, p ≤ 2 * m - 1 → MF21Challenge.UniformOrder m p model.d) ∧
    MF21Challenge.BulkTopOrder m model.d := by
  have hs := tailSymbol_of_tailAngle m hm model htail
  refine ⟨fun k hk ↦ model.d_continuous k, model.d_zero, ?_, bulkTopOrder_of_tailSymbol m model hs⟩
  intro p hp
  exact uniformOrder_of_uniformModelError m p (by omega) model
    (uniformModelError_of_tailSymbol m hm model hs)

end MF21Expansion
#print axioms MF21Expansion.expansion_assertions_of_tailAngle
