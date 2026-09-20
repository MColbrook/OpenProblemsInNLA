import MF21.BulkRootFamily
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Smoothness of the actual factors and phases in the simple-loop
equation, including a smooth desingularized phase at theta = 0. -/

noncomputable section
open Filter
open scoped Topology ContDiff
namespace MF21Bulk

@[fun_prop] theorem unitRoot_contDiff {n : ℕ∞ω} : ContDiff ℝ n unitRoot := by
  change ContDiff ℝ n (fun theta : ℝ => Complex.exp ((theta : ℂ) * Complex.I))
  exact ((Complex.contDiff_exp : ContDiff ℂ n Complex.exp).restrict_scalars ℝ).comp
    (Complex.ofRealCLM.contDiff.mul contDiff_const)

@[fun_prop] theorem spectralBase_contDiff : ContDiff ℝ ∞ spectralBase := by
  change ContDiff ℝ ∞ (fun theta : ℝ => (2 * Real.sin (theta / 2)) ^ 2)
  fun_prop

def phaseFactor (omega : ℂ) (theta : ℝ) : ℂ :=
  1 - stableRoot omega (spectralBase theta) * (unitRoot theta)⁻¹

def rootPhase (omega : ℂ) (theta : ℝ) : ℝ :=
  Complex.arg (phaseFactor omega theta)

theorem phaseFactor_re_pos (omega : ℂ) (theta : ℝ)
    (hs : 0 < spectralBase theta) (homega : ‖omega‖ = 1) (hne : omega ≠ 1) :
    0 < (phaseFactor omega theta).re := by
  have hn := (stableRoot_spec omega (spectralBase theta) hs homega hne).2.1
  have hb := Complex.re_le_norm (stableRoot omega (spectralBase theta) * (unitRoot theta)⁻¹)
  rw [norm_mul, norm_inv, unitRoot_norm, inv_one, mul_one] at hb
  simp only [phaseFactor, Complex.sub_re, Complex.one_re]
  linarith

theorem phaseFactor_contDiffAt (omega : ℂ) (theta : ℝ)
    (hs : 0 < spectralBase theta) (homega : ‖omega‖ = 1) (hne : omega ≠ 1) :
    ContDiffAt ℝ ∞ (phaseFactor omega) theta := by
  have hc := (stableRoot_contDiffAt omega (spectralBase theta) hs homega hne).comp
    theta spectralBase_contDiff.contDiffAt
  exact contDiffAt_const.sub (hc.mul (unitRoot_contDiff.contDiffAt.inv (unitRoot_ne_zero theta)))

theorem arg_contDiffAt_of_re_pos {n : ℕ∞ω} (z : ℂ) (hz : 0 < z.re) :
    ContDiffAt ℝ n Complex.arg z := by
  have hc : ContDiffAt ℝ n Complex.log z :=
    (Complex.contDiffAt_log (Or.inl hz)).restrict_scalars ℝ
  simpa only [Function.comp_def, Complex.imCLM_apply, Complex.log_im] using
    (Complex.imCLM.contDiff.contDiffAt.comp z hc)

theorem rootPhase_contDiffAt (omega : ℂ) (theta : ℝ)
    (hs : 0 < spectralBase theta) (homega : ‖omega‖ = 1) (hne : omega ≠ 1) :
    ContDiffAt ℝ ∞ (rootPhase omega) theta :=
  (arg_contDiffAt_of_re_pos _ (phaseFactor_re_pos omega theta hs homega hne)).comp theta
    (phaseFactor_contDiffAt omega theta hs homega hne)

theorem unitRoot_add (x y : ℝ) : unitRoot (x + y) = unitRoot x * unitRoot y := by
  simp only [unitRoot, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem unitRoot_neg (x : ℝ) : unitRoot (-x) = (unitRoot x)⁻¹ := by
  simp only [unitRoot, Complex.ofReal_neg, neg_mul, Complex.exp_neg]

theorem unitRoot_eq_trig (theta : ℝ) :
    unitRoot theta = (Real.cos theta : ℂ) + (Real.sin theta : ℂ) * Complex.I := by
  rw [unitRoot, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem one_sub_unitRoot_neg (theta : ℝ) :
    1 - unitRoot (-theta) =
      ((2 * Real.sin (theta / 2) : ℝ) : ℂ) * Complex.I * unitRoot (-(theta / 2)) := by
  have hsub : unitRoot (theta / 2) - unitRoot (-(theta / 2)) =
      ((2 * Real.sin (theta / 2) : ℝ) : ℂ) * Complex.I := by
    rw [unitRoot_eq_trig, unitRoot_eq_trig, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [← hsub, sub_mul, ← unitRoot_add, ← unitRoot_add]
  rw [show theta / 2 + -(theta / 2) = 0 by ring,
    show -(theta / 2) + -(theta / 2) = -theta by ring]
  simp [unitRoot]

theorem halfSine_tendsto_pos :
    Tendsto (fun theta : ℝ => 2 * Real.sin (theta / 2)) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : Continuous (fun theta : ℝ => 2 * Real.sin (theta / 2)) := by fun_prop
    have he : Tendsto (fun theta : ℝ => 2 * Real.sin (theta / 2)) (𝓝 0) (𝓝 0) := by
      simpa using (hc.continuousAt (x := 0)).tendsto
    exact he.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin,
      (gt_mem_nhds Real.pi_pos).filter_mono nhdsWithin_le_nhds] with t ht htp
    change 0 < t at ht
    exact mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi (by exact div_pos ht (by norm_num))
      (by linarith))

/-- Exact smooth factor after removing the simple zero of the phase
factor at the lower endpoint. Its endpoint value is kappa + I. -/
theorem phaseFactor_endpoint_factorization_analytic (omega kappa : ℂ)
    (homega : ‖omega‖ = 1) (hne : omega ≠ 1)
    (hk : kappa ^ 2 = -omega) (hkr : 0 < kappa.re) :
    ∃ B : ℝ → ℂ, B 0 = kappa + Complex.I ∧ ContDiffAt ℝ ω B 0 ∧
      ∀ᶠ theta : ℝ in 𝓝[>] 0,
        phaseFactor omega theta = (2 * Real.sin (theta / 2) : ℝ) * B theta := by
  obtain ⟨U, R, hU0, hUc, hRform, _, _, _, hRe⟩ :=
    stableRoot_endpoint_factorization_analytic omega kappa homega hne hk hkr
  let T : ℝ → ℝ := fun theta => 2 * Real.sin (theta / 2)
  let B : ℝ → ℂ := fun theta =>
    Complex.I * unitRoot (-(theta / 2)) - U (T theta) * unitRoot (-theta)
  have hB0 : B 0 = kappa + Complex.I := by
    simp [B, T, unitRoot, hU0]
    ring
  have hBc : ContDiffAt ℝ ω B 0 := by
    have hT : ContDiffAt ℝ ω T 0 := by dsimp [T]; fun_prop
    have hUT : ContDiffAt ℝ ω (fun theta => U (T theta)) 0 := by
      have hc : ContDiffAt ℝ ω U (T 0) := by simpa [T] using hUc
      exact hc.comp 0 hT
    dsimp [B]
    have hneg : ContDiffAt ℝ ω (fun theta : ℝ => -theta) 0 := by fun_prop
    have hhalf : ContDiffAt ℝ ω (fun theta : ℝ => -(theta / 2)) 0 := by fun_prop
    exact (contDiffAt_const.mul (unitRoot_contDiff.contDiffAt.comp 0 hhalf)).sub
      (hUT.mul (unitRoot_contDiff.contDiffAt.comp 0 hneg))
  refine ⟨B, hB0, hBc, ?_⟩
  filter_upwards [halfSine_tendsto_pos.eventually hRe] with theta ht
  have he : stableRoot omega (spectralBase theta) =
      1 + (T theta : ℂ) * U (T theta) := by
    change stableRoot omega ((T theta) ^ 2) = _
    change R (T theta) = stableRoot omega ((T theta) ^ 2) at ht
    rw [← ht, hRform]
  rw [phaseFactor, he, ← unitRoot_neg]
  have hf := one_sub_unitRoot_neg theta
  dsimp [B, T] at *
  linear_combination hf

theorem phaseFactor_endpoint_factorization (omega kappa : ℂ)
    (homega : ‖omega‖ = 1) (hne : omega ≠ 1)
    (hk : kappa ^ 2 = -omega) (hkr : 0 < kappa.re) :
    ∃ B : ℝ → ℂ, B 0 = kappa + Complex.I ∧ ContDiffAt ℝ ∞ B 0 ∧
      ∀ᶠ theta : ℝ in 𝓝[>] 0,
        phaseFactor omega theta = (2 * Real.sin (theta / 2) : ℝ) * B theta := by
  obtain ⟨B, h0, hc, he⟩ := phaseFactor_endpoint_factorization_analytic omega kappa homega hne hk hkr
  exact ⟨B, h0, hc.of_le (by simp), he⟩

/-- The actual principal phase on positive angles has a smooth local
extension through the zero endpoint. -/
theorem rootPhase_endpoint_extension_analytic (omega kappa : ℂ)
    (homega : ‖omega‖ = 1) (hne : omega ≠ 1)
    (hk : kappa ^ 2 = -omega) (hkr : 0 < kappa.re) :
    ∃ P : ℝ → ℝ, P 0 = Complex.arg (kappa + Complex.I) ∧ ContDiffAt ℝ ω P 0 ∧
      ∀ᶠ theta : ℝ in 𝓝[>] 0, P theta = rootPhase omega theta := by
  obtain ⟨B, hB0, hBc, hBe⟩ :=
    phaseFactor_endpoint_factorization_analytic omega kappa homega hne hk hkr
  let P : ℝ → ℝ := fun theta => Complex.arg (B theta)
  have hp : 0 < (B 0).re := by simpa [hB0] using hkr
  refine ⟨P, by simp [P, hB0],
    (arg_contDiffAt_of_re_pos (B 0) hp).comp 0 hBc, ?_⟩
  filter_upwards [hBe, halfSine_tendsto_pos.eventually self_mem_nhdsWithin] with theta he ht
  dsimp [rootPhase, P]
  rw [he, Complex.arg_real_mul _ ht]

theorem rootPhase_endpoint_extension (omega kappa : ℂ)
    (homega : ‖omega‖ = 1) (hne : omega ≠ 1)
    (hk : kappa ^ 2 = -omega) (hkr : 0 < kappa.re) :
    ∃ P : ℝ → ℝ, P 0 = Complex.arg (kappa + Complex.I) ∧ ContDiffAt ℝ ∞ P 0 ∧
      ∀ᶠ theta : ℝ in 𝓝[>] 0, P theta = rootPhase omega theta := by
  obtain ⟨P, h0, hc, he⟩ := rootPhase_endpoint_extension_analytic omega kappa homega hne hk hkr
  exact ⟨P, h0, hc.of_le (by simp), he⟩

theorem unitRoot_add_I_factor (a : ℝ) :
    unitRoot (2 * a - Real.pi / 2) + Complex.I =
      ((2 * Real.sin a : ℝ) : ℂ) * unitRoot a := by
  rw [unitRoot_eq_trig, unitRoot_eq_trig]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, one_mul, mul_one, zero_add, add_zero, sub_zero,
      Real.cos_sub, Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two,
      Real.sin_two_mul, Real.cos_two_mul] <;>
    nlinarith [Real.sin_sq_add_cos_sq a]

theorem kappa_add_I_factor (m : ℕ) (j : Fin m) :
    kappa m j + Complex.I =
      ((2 * Real.sin (Real.pi * j.val / (2 * m)) : ℝ) : ℂ) *
        unitRoot (Real.pi * j.val / (2 * m)) := by
  have he : Real.pi * j.val / m =
      2 * (Real.pi * j.val / (2 * m)) := by ring
  change unitRoot (Real.pi * j.val / m - Real.pi / 2) + Complex.I = _
  rw [he, unitRoot_add_I_factor]

theorem arg_kappa_add_I (m : ℕ) (hm : 0 < m) (j : Fin m) (hj : j.val ≠ 0) :
    Complex.arg (kappa m j + Complex.I) = Real.pi * j.val / (2 * m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hjR : (0 : ℝ) < j.val := by exact_mod_cast Nat.pos_of_ne_zero hj
  have hjm : (j.val : ℝ) < m := by exact_mod_cast j.isLt
  have ha : 0 < Real.pi * j.val / (2 * m) := by positivity
  have hap : Real.pi * j.val / (2 * m) < Real.pi := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * m)).2
    nlinarith [mul_lt_mul_of_pos_left hjm Real.pi_pos]
  rw [kappa_add_I_factor, Complex.arg_real_mul _
    (mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi ha hap)), unitRoot_eq_trig]
  have hangle : Real.pi * j.val / (2 * m) ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨by linarith [Real.pi_pos], hap.le⟩
  simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin] using
    Complex.arg_cos_add_sin_mul_I hangle

theorem stableRoot_conj (omega : ℂ) (s : ℝ)
    (hs : 0 < s) (homega : ‖omega‖ = 1) (hne : omega ≠ 1) :
    stableRoot ((starRingEnd ℂ) omega) s = (starRingEnd ℂ) (stableRoot omega s) := by
  have hconjne : (starRingEnd ℂ) omega ≠ 1 := by
    intro h
    apply hne
    have hh := congrArg (starRingEnd ℂ) h
    simpa using hh
  obtain ⟨hr, hn, he⟩ := stableRoot_spec omega s hs homega hne
  symm
  apply stableRoot_eq_of_spec ((starRingEnd ℂ) omega) _ s hs
    (by simpa using homega) hconjne
  · simpa using hr
  · simpa using hn
  · have hh := congrArg (starRingEnd ℂ) he
    simpa only [map_sub, map_ofNat, map_inv₀, map_mul, Complex.conj_ofReal] using hh

theorem phaseFactor_pi (omega : ℂ) :
    phaseFactor omega Real.pi = 1 + stableRoot omega 4 := by
  have hs : spectralBase Real.pi = 4 := by rw [spectralBase_eq]; norm_num
  have hz : unitRoot Real.pi = -1 := Complex.exp_pi_mul_I
  rw [phaseFactor, hs, hz]
  norm_num

theorem rootPhase_conj_pi (omega : ℂ) (homega : ‖omega‖ = 1) (hne : omega ≠ 1) :
    rootPhase ((starRingEnd ℂ) omega) Real.pi = -rootPhase omega Real.pi := by
  have hp : 0 < (phaseFactor omega Real.pi).re :=
    phaseFactor_re_pos omega Real.pi (by rw [spectralBase_eq]; norm_num) homega hne
  have ha : Complex.arg (phaseFactor omega Real.pi) ≠ Real.pi :=
    ne_of_lt (Complex.arg_lt_pi_iff.mpr (Or.inl hp.le))
  have he : phaseFactor ((starRingEnd ℂ) omega) Real.pi =
      (starRingEnd ℂ) (phaseFactor omega Real.pi) := by
    rw [phaseFactor_pi, phaseFactor_pi, stableRoot_conj omega 4 (by norm_num) homega hne]
    simp
  dsimp [rootPhase]
  rw [he, Complex.arg_conj, if_neg ha]

end MF21Bulk

#print axioms MF21Bulk.phaseFactor_re_pos
#print axioms MF21Bulk.rootPhase_contDiffAt
#print axioms MF21Bulk.phaseFactor_endpoint_factorization
#print axioms MF21Bulk.rootPhase_endpoint_extension
#print axioms MF21Bulk.rootPhase_endpoint_extension_analytic
