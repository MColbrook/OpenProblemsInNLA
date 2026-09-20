import MF21.Eigenangles
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.Order.Round

/-! Quantitative root localization for the perturbed sine equation. The
analytic hypotheses here will be supplied by the normalized boundary determinant. -/

open Set
open scoped Topology
noncomputable section
namespace MF21Phase

theorem sin_quarter_ge_half : (1 : ℝ)/2 ≤ Real.sin (Real.pi/4) := by
  have h := Real.mul_le_sin (x := Real.pi/4) (by positivity) (by linarith [Real.pi_pos])
  have he : 2 / Real.pi * (Real.pi/4) = (1 : ℝ)/2 := by field_simp; norm_num
  rwa [he] at h

theorem cos_ge_half_of_abs_le_quarter {x : ℝ} (hx : |x| ≤ Real.pi/4) :
    (1 : ℝ)/2 ≤ Real.cos x := by
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x)
    (show Real.pi/4 ≤ Real.pi by linarith [Real.pi_pos]) hx
  rw [Real.cos_abs, Real.cos_pi_div_four, ← Real.sin_pi_div_four] at hc
  exact sin_quarter_ge_half.trans hc

theorem phase_cell_derivative_lower {u du de D : ℝ} (hD : 0 < D)
    (hu : |u| ≤ Real.pi/4) (hdu : D ≤ du) (hde : |de| ≤ D/4) :
    D/4 ≤ Real.cos u * du + de := by
  have hc := cos_ge_half_of_abs_le_quarter hu
  have hm := mul_le_mul hc hdu (le_of_lt hD) (by linarith : 0 ≤ Real.cos u)
  have he := (abs_le.mp hde).1
  nlinarith

theorem phase_cell_unique_zero
    (u e du de : ℝ → ℝ) (a b D : ℝ) (hab : a < b) (hD : 0 < D)
    (hua : u a = -Real.pi/4) (hub : u b = Real.pi/4)
    (hu : ∀ x ∈ Icc a b, |u x| ≤ Real.pi/4)
    (hdu : ∀ x ∈ Icc a b, HasDerivAt u (du x) x)
    (hde : ∀ x ∈ Icc a b, HasDerivAt e (de x) x)
    (hdu_lower : ∀ x ∈ Icc a b, D ≤ du x)
    (hde_bound : ∀ x ∈ Icc a b, |de x| ≤ D/4)
    (he_bound : ∀ x ∈ Icc a b, |e x| ≤ (1 : ℝ)/4) :
    (∃! x : ℝ, x ∈ Ioo a b ∧ Real.sin (u x) + e x = 0) ∧
    (∀ x ∈ Icc a b, 0 < deriv (fun t ↦ Real.sin (u t) + e t) x) := by
  let f : ℝ → ℝ := fun x ↦ Real.sin (u x) + e x
  have hd (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt f (Real.cos (u x) * du x + de x) x :=
    (hdu x hx).sin.add (hde x hx)
  have hc : ContinuousOn f (Icc a b) := fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt
  have hpos (x : ℝ) (hx : x ∈ Icc a b) : 0 < deriv f x := by
    rw [(hd x hx).deriv]
    exact (by positivity : 0 < D/4).trans_le
      (phase_cell_derivative_lower hD (hu x hx) (hdu_lower x hx) (hde_bound x hx))
  have hmono : StrictMonoOn f (Icc a b) := strictMonoOn_of_deriv_pos (convex_Icc a b) hc
    (fun x hx ↦ hpos x (interior_subset hx))
  have ha : f a < 0 := by
    have he := (abs_le.mp (he_bound a ⟨le_refl _, le_of_lt hab⟩)).2
    dsimp [f]
    rw [hua, neg_div, Real.sin_neg]
    linarith [sin_quarter_ge_half]
  have hb : 0 < f b := by
    have he := (abs_le.mp (he_bound b ⟨le_of_lt hab, le_refl _⟩)).1
    dsimp [f]
    rw [hub]
    linarith [sin_quarter_ge_half]
  obtain ⟨x, hx, hz⟩ := intermediate_value_Icc (le_of_lt hab) hc ⟨le_of_lt ha, le_of_lt hb⟩
  have hxa : a < x := by
    apply lt_of_le_of_ne hx.1
    intro he
    rw [← he] at hz
    linarith
  have hxb : x < b := by
    apply lt_of_le_of_ne hx.2
    intro he
    rw [he] at hz
    linarith
  refine ⟨⟨x, ⟨⟨hxa, hxb⟩, hz⟩, ?_⟩, hpos⟩
  intro y hy
  exact hmono.injOn ⟨le_of_lt hy.1.1, le_of_lt hy.1.2⟩ hx (hy.2.trans hz.symm)

theorem phase_residual_bound (t E : ℝ) (k : ℕ)
    (hcell : |t - k*Real.pi| ≤ Real.pi/2) (hz : Real.sin t + E = 0) :
    |t - k*Real.pi| ≤ (Real.pi/2) * |E| := by
  have h := Real.mul_abs_le_abs_sin hcell
  rw [Real.sin_sub_nat_mul_pi, abs_mul, abs_pow] at h
  norm_num at h
  have hs : |Real.sin t| = |E| := by
    rw [show Real.sin t = -E by linarith, abs_neg]
  rw [hs] at h
  have hp := mul_le_mul_of_nonneg_left h (le_of_lt Real.pi_pos)
  field_simp at hp
  rw [mul_comm Real.pi (k : ℝ)] at hp
  nlinarith

theorem inverse_phase_displacement
    (F dF : ℝ → ℝ) (a b D : ℝ) (_hD : 0 < D)
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (dF x) x)
    (hdF : ∀ x ∈ Icc a b, D ≤ dF x)
    (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    D * |x-y| ≤ |F x-F y| := by
  have hc : ContinuousOn F (Icc a b) := fun z hz ↦ (hF z hz).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ F (interior (Icc a b)) :=
    fun z hz ↦ (hF z (interior_subset hz)).differentiableAt.differentiableWithinAt
  have hl : ∀ z ∈ interior (Icc a b), D ≤ deriv F z := by
    intro z hz
    rw [(hF z (interior_subset hz)).deriv]
    exact hdF z (interior_subset hz)
  rcases le_total x y with hxy | hyx
  · have hm := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv hc hd hl x hx y hy hxy
    rw [abs_sub_comm x y, abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact hm.trans ((le_abs_self _).trans_eq (abs_sub_comm _ _))
  · have hm := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv hc hd hl y hy x hx hyx
    rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact hm.trans (le_abs_self _)

theorem final_cell_no_root
    (F dF : ℝ → ℝ) (a b D c E x : ℝ) (k : ℕ) (hD : 0 < D)
    (hF : ∀ z ∈ Icc a b, HasDerivAt F (dF z) z)
    (hdF : ∀ z ∈ Icc a b, D ≤ dF z)
    (hx : x ∈ Ico a b) (hFb : F b = k*Real.pi)
    (hcell : |F x-k*Real.pi| ≤ Real.pi/2)
    (hE : |E| ≤ c*(b-x)) (hc : (Real.pi/2)*c < D) :
    Real.sin (F x) + E ≠ 0 := by
  intro hz
  have hres := phase_residual_bound (F x) E k hcell hz
  have hdisp := inverse_phase_displacement F dF a b D hD hF hdF x b
    ⟨hx.1, le_of_lt hx.2⟩ ⟨hx.1.trans (le_of_lt hx.2), le_refl _⟩
  rw [hFb, abs_sub_comm x b, abs_of_pos (sub_pos.mpr hx.2)] at hdisp
  have he := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ Real.pi/2)
  have hlt := mul_lt_mul_of_pos_right hc (sub_pos.mpr hx.2)
  nlinarith

theorem phase_residual_bound_int (t E : ℝ) (k : ℤ)
    (hcell : |t - k*Real.pi| ≤ Real.pi/2) (hz : Real.sin t + E = 0) :
    |t - k*Real.pi| ≤ (Real.pi/2) * |E| := by
  have h := Real.mul_abs_le_abs_sin hcell
  rw [Real.sin_sub_int_mul_pi, abs_mul, abs_zpow] at h
  norm_num at h
  rw [show Real.sin t = -E by linarith, abs_neg] at h
  have hp := mul_le_mul_of_nonneg_left h (le_of_lt Real.pi_pos)
  field_simp at hp
  rw [mul_comm Real.pi (k : ℝ)] at hp
  nlinarith

/-- Small determinant error excludes every gap between phase cells. -/
theorem root_near_integer_phase (t E : ℝ) (hE : |E| ≤ (1 : ℝ)/4)
    (hz : Real.sin t + E = 0) :
    ∃ k : ℤ, |t-k*Real.pi| ≤ Real.pi/8 := by
  let k : ℤ := round (t/Real.pi)
  have hr := abs_sub_round (t/Real.pi)
  have hcell : |t-k*Real.pi| ≤ Real.pi/2 := by
    calc
      _ = |Real.pi * (t/Real.pi-k)| := by
        congr 1
        field_simp
      _ = Real.pi * |t/Real.pi-k| := by rw [abs_mul, abs_of_pos Real.pi_pos]
      _ ≤ Real.pi * (1/2) := mul_le_mul_of_nonneg_left hr (le_of_lt Real.pi_pos)
      _ = _ := by ring
  refine ⟨k, (phase_residual_bound_int t E k hcell hz).trans ?_⟩
  have he := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ Real.pi/2)
  nlinarith

theorem root_phase_index_range (t E : ℝ) (J n : ℕ)
    (hlo : J*Real.pi-Real.pi/4 ≤ t) (hhi : t ≤ (n+1)*Real.pi)
    (hE : |E| ≤ (1 : ℝ)/4) (hz : Real.sin t + E = 0) :
    ∃ k : ℕ, J ≤ k ∧ k ≤ n+1 ∧ |t-k*Real.pi| ≤ Real.pi/8 := by
  obtain ⟨k, hk⟩ := root_near_integer_phase t E hE hz
  have hklo : (J : ℤ) ≤ k := by
    by_contra h
    have h' : k ≤ (J : ℤ)-1 := by omega
    have hc : (k : ℝ) ≤ (J : ℝ)-1 := by exact_mod_cast h'
    have ha := (abs_le.mp hk).2
    nlinarith [Real.pi_pos]
  have hkhi : k ≤ (n+1 : ℕ) := by
    by_contra h
    have h' : (n+2 : ℕ) ≤ k := by omega
    have hc : (n : ℝ)+2 ≤ (k : ℝ) := by exact_mod_cast h'
    have ha := (abs_le.mp hk).1
    nlinarith [Real.pi_pos]
  have hk0 : 0 ≤ k := (Int.natCast_nonneg J).trans hklo
  refine ⟨k.toNat, by omega, by omega, ?_⟩
  have he : (k.toNat : ℝ) = k := by exact_mod_cast Int.toNat_of_nonneg hk0
  simpa only [he] using hk

end MF21Phase

#print axioms MF21Phase.phase_cell_unique_zero
#print axioms MF21Phase.phase_residual_bound
#print axioms MF21Phase.inverse_phase_displacement
#print axioms MF21Phase.final_cell_no_root
#print axioms MF21Phase.root_phase_index_range
