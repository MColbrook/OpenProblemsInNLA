import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic

/-! Existence and uniqueness of the stable characteristic root used in MF-21.
These are proved for every nontrivial unit-modulus omega and every positive
real spectral parameter s. Smooth selection and endpoint estimates remain
separate obligations. -/

noncomputable section
open Filter
open scoped Topology ContDiff
namespace MF21Bulk

theorem no_unit_characteristic_root (omega r : ℂ) (s : ℝ)
    (hs : 0 < s) (homega : ‖omega‖ = 1) (hne : omega ≠ 1)
    (heq : 2 - r - r⁻¹ = omega * s) : ‖r‖ ≠ 1 := by
  intro hr
  rw [Complex.inv_eq_conj hr] at heq
  have hi := congrArg Complex.im heq
  have hre := congrArg Complex.re heq
  norm_num [Complex.sub_im, Complex.conj_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at hi
  norm_num [Complex.sub_re, Complex.conj_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] at hre
  have hoi : omega.im = 0 := hi.resolve_right (ne_of_gt hs)
  have hrr : r.re ≤ 1 := (Complex.re_le_norm r).trans_eq hr
  have hor : 0 ≤ omega.re := by nlinarith
  have hsq := Complex.sq_norm omega
  rw [homega, Complex.normSq_apply, hoi] at hsq
  have hore : omega.re = 1 := by nlinarith
  apply hne
  apply Complex.ext <;> simp_all

theorem characteristic_polynomial (omega r : ℂ) (s : ℝ)
    (hr : r ≠ 0) (heq : 2 - r - r⁻¹ = omega * s) :
    r ^ 2 - (2 - omega * s) * r + 1 = 0 := by
  have h := congrArg (fun z : ℂ => z * r) heq
  field_simp at h
  linear_combination -h

theorem exists_stable_characteristic_root (omega : ℂ) (s : ℝ)
    (hs : 0 < s) (homega : ‖omega‖ = 1) (hne : omega ≠ 1) :
    ∃ r : ℂ, r ≠ 0 ∧ ‖r‖ < 1 ∧ 2 - r - r⁻¹ = omega * s := by
  let A : ℂ := 2 - omega * s
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (A ^ 2 - 4) (by decide : 0 < (2 : ℕ))
  let r : ℂ := (A + z) / 2
  have hp : r ^ 2 - A * r + 1 = 0 := by
    dsimp [r]
    linear_combination hz / 4
  have hr : r ≠ 0 := by
    intro h
    simp [h] at hp
  have heq : 2 - r - r⁻¹ = omega * s := by
    apply (mul_right_cancel₀ hr)
    field_simp
    dsimp [A] at hp
    linear_combination -hp
  by_cases hlt : ‖r‖ < 1
  · exact ⟨r, hr, hlt, heq⟩
  · have hgt : 1 < ‖r‖ :=
      lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm (no_unit_characteristic_root omega r s hs homega hne heq))
    refine ⟨r⁻¹, inv_ne_zero hr, ?_, ?_⟩
    · rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ hgt
    · simpa only [inv_inv] using (show 2 - r⁻¹ - r = omega * s by linear_combination heq)

theorem stable_characteristic_root_unique (omega r q : ℂ) (s : ℝ)
    (hr : r ≠ 0) (hq : q ≠ 0) (hrr : ‖r‖ < 1) (hqr : ‖q‖ < 1)
    (her : 2 - r - r⁻¹ = omega * s)
    (heq : 2 - q - q⁻¹ = omega * s) : r = q := by
  have hpr := characteristic_polynomial omega r s hr her
  have hpq := characteristic_polynomial omega q s hq heq
  have hprod : (r - q) * (r * q - 1) = 0 := by
    linear_combination q * hpr - r * hpq
  rcases mul_eq_zero.mp hprod with h | h
  · exact sub_eq_zero.mp h
  · have he : r * q = 1 := sub_eq_zero.mp h
    have hn : ‖r * q‖ < 1 := by
      rw [norm_mul]
      calc
        _ ≤ ‖r‖ * 1 := mul_le_mul_of_nonneg_left hqr.le (norm_nonneg _)
        _ = ‖r‖ := mul_one _
        _ < 1 := hrr
    simp [he] at hn

/-- The stable root is simple, so the implicit-function theorem can apply
at every strictly positive spectral parameter. -/
theorem stable_characteristic_root_simple (omega r : ℂ) (s : ℝ)
    (hr : r ≠ 0) (hrr : ‖r‖ < 1)
    (her : 2 - r - r⁻¹ = omega * s) :
    2 * r - (2 - omega * s) ≠ 0 := by
  intro hd
  have hp := characteristic_polynomial omega r s hr her
  have he : r ^ 2 = 1 := by linear_combination -hp + r * hd
  have hn := congrArg norm he
  rw [norm_pow, norm_one] at hn
  nlinarith [norm_nonneg r]

/-- The uniquely specified stable branch, with zero outside its domain. -/
def stableRoot (omega : ℂ) (s : ℝ) : ℂ :=
  if h : 0 < s ∧ ‖omega‖ = 1 ∧ omega ≠ 1 then
    (exists_stable_characteristic_root omega s h.1 h.2.1 h.2.2).choose
  else 0

theorem stableRoot_spec (omega : ℂ) (s : ℝ)
    (hs : 0 < s) (homega : ‖omega‖ = 1) (hne : omega ≠ 1) :
    stableRoot omega s ≠ 0 ∧ ‖stableRoot omega s‖ < 1 ∧
      2 - stableRoot omega s - (stableRoot omega s)⁻¹ = omega * s := by
  rw [stableRoot, dif_pos ⟨hs, homega, hne⟩]
  exact (exists_stable_characteristic_root omega s hs homega hne).choose_spec

theorem stableRoot_eq_of_spec (omega r : ℂ) (s : ℝ)
    (hs : 0 < s) (homega : ‖omega‖ = 1) (hne : omega ≠ 1)
    (hr : r ≠ 0) (hrr : ‖r‖ < 1)
    (her : 2 - r - r⁻¹ = omega * s) :
    r = stableRoot omega s := by
  obtain ⟨hz, hn, he⟩ := stableRoot_spec omega s hs homega hne
  exact stable_characteristic_root_unique omega r (stableRoot omega s) s hr hz hrr hn her he

/-- Analytic local selection of a simple root of the actual reciprocal
characteristic polynomial, with both root and spectral parameter complex. -/
theorem local_characteristic_root (omega s r : ℂ)
    (hp : r ^ 2 - (2 - omega * s) * r + 1 = 0)
    (hsimple : 2 * r - (2 - omega * s) ≠ 0) :
    ∃ R : ℂ → ℂ, R s = r ∧ ContDiffAt ℂ ∞ R s ∧
      ∀ᶠ t : ℂ in 𝓝 s, (R t) ^ 2 - (2 - omega * t) * R t + 1 = 0 := by
  let F : ℂ × ℂ → ℂ := fun p => p.2 ^ 2 - (2 - omega * p.1) * p.2 + 1
  have hc : ContDiffAt ℂ ∞ F (s, r) := by dsimp [F]; fun_prop
  let d := 2 * r - (2 - omega * s)
  have hd : HasDerivAt (fun z : ℂ => z ^ 2 - (2 - omega * s) * z + 1) d r := by
    simpa [d] using (((hasDerivAt_id r).pow 2).sub
      ((hasDerivAt_id r).const_mul (2 - omega * s))).add_const 1
  have hpartial : fderiv ℂ F (s, r) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ =
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d := by
    have hcomp := (hc.differentiableAt (by simp)).hasFDerivAt.comp r
      ((hasFDerivAt_const s r).prodMk (hasFDerivAt_id r))
    have hpoly : HasFDerivAt (fun z : ℂ => z ^ 2 - (2 - omega * s) * z + 1)
        (fderiv ℂ F (s, r) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ) r := by
      simpa [F, Function.comp_def, ContinuousLinearMap.inr] using hcomp
    exact hpoly.unique hd.hasFDerivAt
  have hinv : (fderiv ℂ F (s, r) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
    rw [hpartial]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 d hsimple), ?_⟩
    rfl
  let R := hc.implicitFunction (by simp) hinv
  refine ⟨R, hc.implicitFunction_apply_self (by simp) hinv,
    hc.contDiffAt_implicitFunction (by simp) hinv, ?_⟩
  filter_upwards [hc.eventually_apply_implicitFunction (by simp) hinv] with t ht
  simpa only [F, hp] using ht

/-- The canonical stable branch is smooth at every positive spectral
parameter; this is a property of the actual branch defined above. -/
theorem stableRoot_contDiffAt (omega : ℂ) (s : ℝ)
    (hs : 0 < s) (homega : ‖omega‖ = 1) (hne : omega ≠ 1) :
    ContDiffAt ℝ ∞ (stableRoot omega) s := by
  obtain ⟨hr, hn, he⟩ := stableRoot_spec omega s hs homega hne
  obtain ⟨R, hR0, hRc, hRe⟩ := local_characteristic_root omega (s : ℂ)
    (stableRoot omega s)
    (characteristic_polynomial omega (stableRoot omega s) s hr he)
    (stable_characteristic_root_simple omega (stableRoot omega s) s hr hn he)
  let Rc : ℝ → ℂ := fun t => R (t : ℂ)
  have hc : ContDiffAt ℝ ∞ Rc s :=
    (hRc.restrict_scalars ℝ).comp s Complex.ofRealCLM.contDiff.contDiffAt
  have hpoly : ∀ᶠ t : ℝ in 𝓝 s,
      (Rc t) ^ 2 - (2 - omega * t) * Rc t + 1 = 0 :=
    Complex.continuous_ofReal.continuousAt.tendsto.eventually hRe
  have hns : ‖Rc s‖ < 1 := by simpa only [Rc, hR0] using hn
  have hnorm : ∀ᶠ t : ℝ in 𝓝 s, ‖Rc t‖ < 1 :=
    hc.continuousAt.norm.tendsto.eventually (gt_mem_nhds hns)
  apply hc.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hs, hpoly, hnorm] with t ht hp hnt
  have hrt : Rc t ≠ 0 := by intro hz; simp [hz] at hp
  have het : 2 - Rc t - (Rc t)⁻¹ = omega * t := by
    apply mul_right_cancel₀ hrt
    field_simp
    linear_combination -hp
  exact (stableRoot_eq_of_spec omega (Rc t) t ht homega hne hrt hnt het).symm

end MF21Bulk

#print axioms MF21Bulk.no_unit_characteristic_root
#print axioms MF21Bulk.exists_stable_characteristic_root
#print axioms MF21Bulk.stable_characteristic_root_unique
#print axioms MF21Bulk.stable_characteristic_root_simple
#print axioms MF21Bulk.stableRoot_spec
#print axioms MF21Bulk.local_characteristic_root
#print axioms MF21Bulk.stableRoot_contDiffAt
