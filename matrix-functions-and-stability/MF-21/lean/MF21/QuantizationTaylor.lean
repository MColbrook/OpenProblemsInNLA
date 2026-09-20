import MF21.UniformQuantization
import MF21.BulkEta

/-! The actual MF-21 phase yields one coefficient family for all Taylor orders. -/
noncomputable section
open Filter Set Finset
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency.types false
namespace MF21Quantization

/-- Data produced from the actual root-defined phase, not a surrogate quantization assumption. -/
structure Model (m : ℕ) where
  eta : ℝ → ℝ
  H : ℝ
  Hpos : 0 < H
  Y : ℝ × ℝ → ℝ
  eta_cont : ContinuousAt eta 0
  eta_smooth : ∀ theta ∈ Icc 0 Real.pi, ContDiffAt ℝ ∞ eta theta
  eta_zero : eta 0 = (m - 1 : ℝ) * Real.pi / 2
  eta_pi : eta Real.pi = Real.pi
  eta_actual : ∀ theta > 0, eta theta = theta + 2 * MF21Bulk.psi m theta
  smooth : ∀ p ∈ Icc 0 Real.pi ×ˢ Icc 0 H, ContDiffAt ℝ ∞ Y p
  equation : ∀ p ∈ Icc 0 Real.pi ×ˢ Icc 0 H, Y p = p.1 + p.2 * eta (Y p)
  inverse_distance : ∀ p ∈ Icc 0 Real.pi ×ˢ Icc 0 H, ∀ theta ∈ Icc 0 Real.pi,
    |Y p - theta| ≤ 2 * |p.1 - (theta - p.2 * eta theta)|
  below : ∀ p ∈ Icc 0 Real.pi ×ˢ Icc 0 H, ∀ theta ∈ Icc 0 Real.pi,
    p.1 < theta - p.2 * eta theta → Y p < theta
  above : ∀ p ∈ Icc 0 Real.pi ×ˢ Icc 0 H, ∀ theta ∈ Icc 0 Real.pi,
    theta - p.2 * eta theta < p.1 → theta < Y p

theorem model_exists (m : ℕ) (hm : 0 < m) : Nonempty (Model m) := by
  obtain ⟨eta, delta, hd, he, he0, hep, hea⟩ := MF21Bulk.eta_extension m hm
  obtain ⟨H, hH, hY⟩ := exists_uniform_smooth_lipschitz_inverse eta (-delta) (Real.pi + delta)
    0 Real.pi Real.pi_pos.le (by linarith) (by linarith) he
  exact ⟨{
    eta := eta, H := H, Hpos := hH,
    Y := intervalInverse eta (-delta) (Real.pi + delta),
    eta_cont := (he 0 ⟨by linarith, by linarith [Real.pi_pos]⟩).continuousAt,
    eta_smooth := fun theta ht ↦ he theta ⟨by linarith [ht.1], by linarith [ht.2]⟩,
    eta_zero := he0, eta_pi := hep, eta_actual := hea,
    smooth := fun p hp ↦ (hY p hp).2.2.1,
    equation := fun p hp ↦ (hY p hp).2.1,
    inverse_distance := fun p hp theta ht ↦ ((hY p hp).2.2.2 theta
      ⟨by linarith [ht.1], by linarith [ht.2]⟩).1,
    below := fun p hp theta ht ↦ ((hY p hp).2.2.2 theta
      ⟨by linarith [ht.1], by linarith [ht.2]⟩).2.2,
    above := fun p hp theta ht ↦ ((hY p hp).2.2.2 theta
      ⟨by linarith [ht.1], by linarith [ht.2]⟩).2.1 }⟩

def actualModel (m : ℕ) (hm : 0 < m) : Model m := Classical.choice (model_exists m hm)

def Model.F {m : ℕ} (model : Model m) (p : ℝ × ℝ) : ℝ :=
  MF21Challenge.symbol m (model.Y p)

def Model.d {m : ℕ} (model : Model m) : MF21Challenge.Coefficients :=
  MF21Taylor.coefficient model.F

theorem symbol_contDiff (m : ℕ) : ContDiff ℝ ∞ (MF21Challenge.symbol m) := by
  unfold MF21Challenge.symbol
  exact (contDiff_const.mul (Real.contDiff_sin.comp (contDiff_id.div_const 2))).pow _

theorem Model.F_smooth {m : ℕ} (model : Model m)
    (p : ℝ × ℝ) (hp : p ∈ Icc 0 Real.pi ×ˢ Icc 0 model.H) :
    ContDiffAt ℝ ∞ model.F p :=
  (symbol_contDiff m).contDiffAt.comp p (model.smooth p hp)

theorem Model.zero_slice {m : ℕ} (model : Model m) (s : ℝ) (hs : s ∈ Icc 0 Real.pi) :
    model.Y (s, 0) = s := by
  simpa only [zero_mul, add_zero] using model.equation (s, 0) ⟨hs, le_rfl, model.Hpos.le⟩

theorem Model.d_continuous {m : ℕ} (model : Model m) (k : ℕ) :
    ContinuousOn (model.d k) (Icc 0 Real.pi) :=
  MF21Taylor.coefficient_continuousOn model.F 0 Real.pi
    (fun s hs ↦ model.F_smooth (s, 0) ⟨hs, le_rfl, model.Hpos.le⟩) k

theorem Model.d_smooth {m : ℕ} (model : Model m) (k : ℕ)
    (s : ℝ) (hs : s ∈ Icc 0 Real.pi) : ContDiffAt ℝ ∞ (model.d k) s :=
  MF21Taylor.coefficient_contDiffAt model.F k s
    (model.F_smooth (s, 0) ⟨hs, le_rfl, model.Hpos.le⟩)

theorem Model.d_zero {m : ℕ} (model : Model m) (s : ℝ) (hs : s ∈ Icc 0 Real.pi) :
    model.d 0 s = MF21Challenge.symbol m s := by
  rw [Model.d, MF21Taylor.coefficient_zero, Model.F, model.zero_slice s hs]

theorem Model.uniform_taylor {m : ℕ} (model : Model m) (p : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ s ∈ Icc 0 Real.pi, ∀ h ∈ Icc 0 model.H,
      |model.F (s, h) - ∑ k ∈ range (p + 1), model.d k s * h ^ k| ≤ D * h ^ (p + 1) :=
  MF21Taylor.uniform_taylor_bound_on model.F 0 Real.pi model.H model.Hpos model.F_smooth p

/-- At every fixed source index the exact implicit model has the shifted power
profile. Only equations along the strip are needed, including at the endpoint. -/
theorem Model.fixed_index_profile {m : ℕ} (model : Model m) (c : ℝ)
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (hmem : ∀ᶠ n in atTop, c * h n ∈ Icc 0 Real.pi ∧ h n ∈ Ioc 0 model.H) :
    Tendsto (fun n ↦ model.F (c * h n, h n) / h n ^ (2 * m))
      atTop (𝓝 ((c + (m - 1 : ℝ) * Real.pi / 2) ^ (2 * m))) := by
  have hY0 : model.Y (0, 0) = 0 := model.zero_slice 0 ⟨le_rfl, Real.pi_pos.le⟩
  have hp : Tendsto (fun n ↦ (c * h n, h n)) atTop (𝓝 ((0 : ℝ), (0 : ℝ))) := by
    simpa only [mul_zero] using (hh.const_mul c).prodMk_nhds hh
  have hc : ContinuousAt model.Y (0, 0) :=
    (model.smooth (0, 0) ⟨⟨le_rfl, Real.pi_pos.le⟩, le_rfl, model.Hpos.le⟩).continuousAt
  have hy : Tendsto (fun n ↦ model.Y (c * h n, h n)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, hY0] using hc.tendsto.comp hp
  have hratio : Tendsto (fun n ↦ model.Y (c * h n, h n) / h n)
      atTop (𝓝 (c + model.eta 0)) := by
    apply ((model.eta_cont.tendsto.comp hy).const_add c).congr'
    filter_upwards [hmem] with n hn
    have he := model.equation (c * h n, h n) ⟨hn.1, hn.2.1.le, hn.2.2⟩
    change c + model.eta (model.Y (c * h n, h n)) = model.Y (c * h n, h n) / h n
    rw [eq_div_iff (ne_of_gt hn.2.1)]
    linear_combination -he
  simpa only [Model.F, model.eta_zero] using symbol_scaled_tendsto m _ h _ hy hratio

/-- The same fixed-index profile holds for the order-2m Taylor approximant. -/
theorem Model.coefficient_fixed_index_profile {m : ℕ} (model : Model m) (c : ℝ)
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (hmem : ∀ᶠ n in atTop, c * h n ∈ Icc 0 Real.pi ∧ h n ∈ Ioc 0 model.H) :
    Tendsto (fun n ↦ (∑ k ∈ range (2 * m + 1), model.d k (c * h n) * h n ^ k) /
      h n ^ (2 * m)) atTop (𝓝 ((c + (m - 1 : ℝ) * Real.pi / 2) ^ (2 * m))) :=
  MF21Taylor.taylor_profile_tendsto model.F 0 Real.pi model.H model.Hpos model.F_smooth
    (2 * m) (fun n ↦ c * h n) h hh hmem _ (model.fixed_index_profile c h hh hmem)


/-- Finite source indices satisfy the lower-order expansion bounds without
requiring separate endpoint-vanishing identities for every coefficient. -/
theorem Model.fixed_index_low_order_bound {m : ℕ} (model : Model m) (p : ℕ)
    (hp : p + 1 ≤ 2 * m) (c : ℝ) (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (hmem : ∀ᶠ n in atTop, c * h n ∈ Icc 0 Real.pi ∧ h n ∈ Ioc 0 model.H) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n in atTop,
      |∑ k ∈ range (p + 1), model.d k (c * h n) * h n ^ k| ≤ D * h n ^ (p + 1) := by
  obtain ⟨D₀, hD₀, hb⟩ := model.uniform_taylor p
  let L : ℝ := (c + (m - 1 : ℝ) * Real.pi / 2) ^ (2 * m)
  have hL := (model.fixed_index_profile c h hh hmem).abs.eventually_lt_const
    (show |L| < |L| + 1 by linarith)
  have hh1 := hh.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)
  refine ⟨D₀ + |L| + 1, by positivity, ?_⟩
  filter_upwards [hmem, hL, hh1] with n hn hLn hn1
  have hf : |model.F (c * h n, h n)| ≤ (|L| + 1) * h n ^ (2 * m) := by
    rw [abs_div, abs_of_pos (pow_pos hn.2.1 (2 * m))] at hLn
    exact ((div_lt_iff₀ (pow_pos hn.2.1 (2 * m))).mp hLn).le
  have hpow : h n ^ (2 * m) ≤ h n ^ (p + 1) :=
    pow_le_pow_of_le_one hn.2.1.le hn1.le hp
  have he := hb (c * h n) hn.1 (h n) ⟨hn.2.1.le, hn.2.2⟩
  calc
    _ = |((∑ k ∈ range (p + 1), model.d k (c * h n) * h n ^ k) -
        model.F (c * h n, h n)) + model.F (c * h n, h n)| := by ring_nf
    _ ≤ |(∑ k ∈ range (p + 1), model.d k (c * h n) * h n ^ k) -
        model.F (c * h n, h n)| + |model.F (c * h n, h n)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_sub_comm]
      nlinarith [mul_le_mul_of_nonneg_left hpow (show 0 ≤ |L| + 1 by positivity)]

end MF21Quantization
#print axioms MF21Quantization.model_exists
#print axioms MF21Quantization.Model.uniform_taylor
#print axioms MF21Quantization.Model.coefficient_fixed_index_profile

#print axioms MF21Quantization.Model.d_smooth
#print axioms MF21Quantization.Model.fixed_index_low_order_bound
