import MF21Restart.ActualSimpleRoots
import MF21Restart.SpectralWindowBounds
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Existence, uniqueness, and simplicity of an actual residual zero in each
sufficiently high phase window. The original eigenvalue index is not yet
identified with the phase label. See `PHASE_WINDOW_ROOTS_STATEMENTS.md`.
-/

set_option autoImplicit false
noncomputable section

namespace MF21Restart

private theorem phase_cos_gt_quarter (x : ℝ) (hx : |x| ≤ Real.pi / 4) :
    (1 / 4 : ℝ) < Real.cos x := by
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x)
    (by linarith [Real.pi_pos] : Real.pi / 4 ≤ Real.pi) hx
  rw [Real.cos_abs] at hcos
  have hmargin : (1 / 4 : ℝ) < Real.cos (Real.pi / 4) := by
    simpa only [Real.sin_pi_div_four, Real.cos_pi_div_four] using phase_window_margin
  exact hmargin.trans_le hcos

private def scaledPhaseResidual (F E : ℝ → ℝ) (k : ℕ) (θ : ℝ) : ℝ :=
  (-1 : ℝ) ^ k * (Real.sin (F θ) + E θ)

private theorem scaledPhaseResidual_eq (F E : ℝ → ℝ) (k : ℕ) (θ : ℝ) :
    scaledPhaseResidual F E k θ =
      Real.sin (F θ - (k : ℝ) * Real.pi) + (-1 : ℝ) ^ k * E θ := by
  rw [Real.sin_sub_nat_mul_pi]
  unfold scaledPhaseResidual
  ring

private theorem scaledPhaseResidual_hasDerivAt
    (F E : ℝ → ℝ) (k : ℕ) (θ : ℝ)
    (hF : HasDerivAt F (deriv F θ) θ) (hE : HasDerivAt E (deriv E θ) θ) :
    HasDerivAt (scaledPhaseResidual F E k)
      (Real.cos (F θ - (k : ℝ) * Real.pi) * deriv F θ +
        (-1 : ℝ) ^ k * deriv E θ) θ := by
  convert! ((hF.sin.add hE).const_mul ((-1 : ℝ) ^ k)) using 1 <;>
    simp only [scaledPhaseResidual, Real.cos_sub_nat_mul_pi] <;> ring

private theorem scaledPhaseResidual_deriv_pos
    (F E : ℝ → ℝ) (A : ℝ) (k : ℕ) (θ : ℝ) (hA : 0 < A)
    (hF : HasDerivAt F (deriv F θ) θ) (hE : HasDerivAt E (deriv E θ) θ)
    (hFlo : A / 2 ≤ deriv F θ)
    (hcell : |F θ - (k : ℝ) * Real.pi| ≤ Real.pi / 4)
    (hEsmall : |deriv E θ| < A / 8) :
    0 < deriv (scaledPhaseResidual F E k) θ := by
  rw [(scaledPhaseResidual_hasDerivAt F E k θ hF hE).deriv]
  have hcos := phase_cos_gt_quarter _ hcell
  have hFpos : 0 < deriv F θ := (half_pos hA).trans_le hFlo
  have hmain : A / 8 < Real.cos (F θ - (k : ℝ) * Real.pi) * deriv F θ := by
    calc
      A / 8 = (1 / 4 : ℝ) * (A / 2) := by ring
      _ ≤ (1 / 4 : ℝ) * deriv F θ := mul_le_mul_of_nonneg_left hFlo (by norm_num)
      _ < Real.cos (F θ - (k : ℝ) * Real.pi) * deriv F θ :=
        mul_lt_mul_of_pos_right hcos hFpos
  have hsE : |(-1 : ℝ) ^ k * deriv E θ| < A / 8 := by
    simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using hEsmall
  linarith [(abs_lt.mp hsE).1]

/-- The scalar calculus argument. Every hypothesis is discharged by the
actual functions in the public theorem below. -/
private theorem phase_window_unique_zero
    (F E : ℝ → ℝ) (A : ℝ) (k : ℕ) (hA : 0 < A)
    (hF : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi, HasDerivAt F (deriv F θ) θ)
    (hE : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi, HasDerivAt E (deriv E θ) θ)
    (hFlo : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi, A / 2 ≤ deriv F θ)
    (hleft : F 0 < (k : ℝ) * Real.pi - Real.pi / 4)
    (hright : (k : ℝ) * Real.pi + Real.pi / 4 < F Real.pi)
    (hsmall : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      |F θ - (k : ℝ) * Real.pi| ≤ Real.pi / 4 →
        |E θ| < 1 / 4 ∧ |deriv E θ| < A / 8) :
    (∃! θ : ℝ, θ ∈ Set.Ioo 0 Real.pi ∧
      |F θ - (k : ℝ) * Real.pi| ≤ Real.pi / 4 ∧ Real.sin (F θ) + E θ = 0) ∧
    ∀ θ : ℝ, θ ∈ Set.Ioo 0 Real.pi →
      |F θ - (k : ℝ) * Real.pi| ≤ Real.pi / 4 →
      deriv (fun t : ℝ => Real.sin (F t) + E t) θ ≠ 0 := by
  have hFcont : ContinuousOn F (Set.Icc 0 Real.pi) :=
    fun θ hθ => (hF θ hθ).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn F (Set.Icc 0 Real.pi) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 Real.pi) hFcont
    intro θ hθ
    exact (half_pos hA).trans_le
      (hFlo θ (Set.mem_of_mem_of_subset hθ interior_subset))
  have hlevels : (k : ℝ) * Real.pi - Real.pi / 4 <
      (k : ℝ) * Real.pi + Real.pi / 4 := by linarith [Real.pi_pos]
  obtain ⟨a, ha, haF⟩ := intermediate_value_Icc Real.pi_pos.le hFcont
    (show (k : ℝ) * Real.pi - Real.pi / 4 ∈ Set.Icc (F 0) (F Real.pi) from
      ⟨hleft.le, (hlevels.trans hright).le⟩)
  obtain ⟨b, hb, hbF⟩ := intermediate_value_Icc Real.pi_pos.le hFcont
    (show (k : ℝ) * Real.pi + Real.pi / 4 ∈ Set.Icc (F 0) (F Real.pi) from
      ⟨(hleft.trans hlevels).le, hright.le⟩)
  have ha0 : 0 < a :=
    (hmono.lt_iff_lt ⟨le_rfl, Real.pi_pos.le⟩ ha).mp (by rw [haF]; exact hleft)
  have hbπ : b < Real.pi :=
    (hmono.lt_iff_lt hb ⟨Real.pi_pos.le, le_rfl⟩).mp (by rw [hbF]; exact hright)
  have hab : a < b :=
    (hmono.lt_iff_lt ha hb).mp (by rw [haF, hbF]; exact hlevels)
  have hmem (θ : ℝ) (hθ : θ ∈ Set.Icc a b) : θ ∈ Set.Icc 0 Real.pi :=
    ⟨ha.1.trans hθ.1, hθ.2.trans hb.2⟩
  have hcellOn (θ : ℝ) (hθ : θ ∈ Set.Icc a b) :
      |F θ - (k : ℝ) * Real.pi| ≤ Real.pi / 4 := by
    have hl := hmono.monotoneOn ha (hmem θ hθ) hθ.1
    have hu := hmono.monotoneOn (hmem θ hθ) hb hθ.2
    rw [haF] at hl
    rw [hbF] at hu
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hcell_mem (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi)
      (hc : |F θ - (k : ℝ) * Real.pi| ≤ Real.pi / 4) : θ ∈ Set.Icc a b := by
    constructor
    · apply (hmono.le_iff_le ha hθ).mp
      rw [haF]
      linarith [(abs_le.mp hc).1]
    · apply (hmono.le_iff_le hθ hb).mp
      rw [hbF]
      linarith [(abs_le.mp hc).2]
  have hdR (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi)
      (hc : |F θ - (k : ℝ) * Real.pi| ≤ Real.pi / 4) :
      0 < deriv (scaledPhaseResidual F E k) θ :=
    scaledPhaseResidual_deriv_pos F E A k θ hA (hF θ hθ) (hE θ hθ)
      (hFlo θ hθ) hc (hsmall θ hθ hc).2
  have hRcont : ContinuousOn (scaledPhaseResidual F E k) (Set.Icc a b) := by
    intro θ hθ
    exact (scaledPhaseResidual_hasDerivAt F E k θ
      (hF θ (hmem θ hθ)) (hE θ (hmem θ hθ))).continuousAt.continuousWithinAt
  have hRmono : StrictMonoOn (scaledPhaseResidual F E k) (Set.Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b) hRcont
    intro θ hθ
    have hi : θ ∈ Set.Icc a b := Set.mem_of_mem_of_subset hθ interior_subset
    exact hdR θ (hmem θ hi) (hcellOn θ hi)
  have hEa : |(-1 : ℝ) ^ k * E a| < 1 / 4 := by
    simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using
      (hsmall a ha (hcellOn a ⟨le_rfl, hab.le⟩)).1
  have hEb : |(-1 : ℝ) ^ k * E b| < 1 / 4 := by
    simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using
      (hsmall b hb (hcellOn b ⟨hab.le, le_rfl⟩)).1
  have hRa : scaledPhaseResidual F E k a < 0 := by
    rw [scaledPhaseResidual_eq, haF]
    have hoff : ((k : ℝ) * Real.pi - Real.pi / 4) - (k : ℝ) * Real.pi =
        -(Real.pi / 4) := by ring
    rw [hoff, Real.sin_neg]
    linarith [phase_window_margin, (abs_lt.mp hEa).2]
  have hRb : 0 < scaledPhaseResidual F E k b := by
    rw [scaledPhaseResidual_eq, hbF]
    have hoff : ((k : ℝ) * Real.pi + Real.pi / 4) - (k : ℝ) * Real.pi =
        Real.pi / 4 := by ring
    rw [hoff]
    linarith [phase_window_margin, (abs_lt.mp hEb).1]
  obtain ⟨θ, hθ, hRzero⟩ := intermediate_value_Icc hab.le hRcont ⟨hRa.le, hRb.le⟩
  have hHθ : Real.sin (F θ) + E θ = 0 := by
    change (-1 : ℝ) ^ k * (Real.sin (F θ) + E θ) = 0 at hRzero
    exact (mul_eq_zero.mp hRzero).resolve_left (pow_ne_zero _ (by norm_num))
  constructor
  · refine ⟨θ, ⟨⟨ha0.trans_le hθ.1, hθ.2.trans_lt hbπ⟩, hcellOn θ hθ, hHθ⟩, ?_⟩
    intro φ hφ
    have hφab := hcell_mem φ ⟨hφ.1.1.le, hφ.1.2.le⟩ hφ.2.1
    apply hRmono.injOn hφab hθ
    change (-1 : ℝ) ^ k * (Real.sin (F φ) + E φ) =
      (-1 : ℝ) ^ k * (Real.sin (F θ) + E θ)
    rw [hφ.2.2, hHθ]
  · intro φ hφ hc
    have hφcc : φ ∈ Set.Icc 0 Real.pi := ⟨hφ.1.le, hφ.2.le⟩
    have hdpos := hdR φ hφcc hc
    have hHderiv := ((hF φ hφcc).sin.add (hE φ hφcc)).differentiableAt.hasDerivAt
    have hRderiv := hHderiv.const_mul ((-1 : ℝ) ^ k)
    have hReq : deriv (scaledPhaseResidual F E k) φ =
        (-1 : ℝ) ^ k * deriv (fun t : ℝ => Real.sin (F t) + E t) φ := hRderiv.deriv
    rw [hReq] at hdpos
    exact (mul_ne_zero_iff.mp (ne_of_gt hdpos)).2

/-- Uniform actual phase-window roots, before any identification of the
window label with an original ordered eigenvalue index. -/
theorem manuscriptResidual_unique_root_in_phase_windows (m : ℕ) (hm : 2 ≤ m) :
    ∃ N J : ℕ, 1 ≤ N ∧ 1 ≤ J ∧
      ∀ n : ℕ, N ≤ n → ∀ k : ℕ, J ≤ k → k ≤ n →
        (∃! θ : ℝ, θ ∈ Set.Ioo 0 Real.pi ∧
          |manuscriptPhaseFn m n θ - (k : ℝ) * Real.pi| ≤ Real.pi / 4 ∧
          manuscriptResidual m n hm θ = 0) ∧
        ∀ θ : ℝ, θ ∈ Set.Ioo 0 Real.pi →
          |manuscriptPhaseFn m n θ - (k : ℝ) * Real.pi| ≤ Real.pi / 4 →
          deriv (manuscriptResidual m n hm) θ ≠ 0 := by
  obtain ⟨N, hN⟩ := manuscriptPhaseFn_eventual_derivative_bounds m (by omega)
  obtain ⟨J, hJ, hEsmall⟩ := manuscriptError_high_phase_small m hm
  refine ⟨max N 1, J, le_max_right _ _, hJ, ?_⟩
  intro n hn k hJk hkn
  have hnN : N ≤ n := (le_max_left N 1).trans hn
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hJ.trans hJk
  have hknr : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hJkr : (J : ℝ) ≤ k := by exact_mod_cast hJk
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hF (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi) :
      HasDerivAt (manuscriptPhaseFn m n) (deriv (manuscriptPhaseFn m n) θ) θ :=
    (manuscriptPhaseFn_hasDerivAt m n (by omega) θ hθ).differentiableAt.hasDerivAt
  have hE (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi) :
      HasDerivAt (manuscriptError m n hm) (deriv (manuscriptError m n hm) θ) θ :=
    ((manuscriptError_contDiffAt m n hm θ hθ).differentiableAt (by simp)).hasDerivAt
  have hleft : manuscriptPhaseFn m n 0 < (k : ℝ) * Real.pi - Real.pi / 4 := by
    have hzero : manuscriptPhaseFn m n 0 ≤ 0 := by
      rw [manuscriptPhaseFn_zero m n (by omega)]
      exact neg_nonpos.mpr (div_nonneg
        (mul_nonneg (by linarith : 0 ≤ (m : ℝ) - 1) Real.pi_pos.le) (by norm_num))
    have hkpi := mul_le_mul_of_nonneg_right hk1 Real.pi_pos.le
    linarith [Real.pi_pos]
  have hright : (k : ℝ) * Real.pi + Real.pi / 4 < manuscriptPhaseFn m n Real.pi := by
    rw [manuscriptPhaseFn_pi m n (by omega)]
    have hkpi := mul_le_mul_of_nonneg_right hknr Real.pi_pos.le
    nlinarith only [hkpi, Real.pi_pos]
  have hsmall (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi)
      (hc : |manuscriptPhaseFn m n θ - (k : ℝ) * Real.pi| ≤ Real.pi / 4) :
      |manuscriptError m n hm θ| < 1 / 4 ∧
        |deriv (manuscriptError m n hm) θ| < (n + 2 : ℝ) / 8 := by
    apply hEsmall n θ hθ.1 hθ.2
    have hJkpi := mul_le_mul_of_nonneg_right hJkr Real.pi_pos.le
    linarith [(abs_le.mp hc).1]
  exact
    phase_window_unique_zero (manuscriptPhaseFn m n) (manuscriptError m n hm)
      (n + 2 : ℝ) k (by positivity) hF hE
      (fun θ hθ => (hN n hnN θ hθ).1) hleft hright hsmall

#print axioms manuscriptResidual_unique_root_in_phase_windows

end MF21Restart
