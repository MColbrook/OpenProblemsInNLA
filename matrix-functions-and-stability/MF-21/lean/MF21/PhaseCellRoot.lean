import MF21.PerturbedPhase

open Set
open scoped Topology
noncomputable section
namespace MF21Phase

theorem phase_cell_endpoints (F dF : ℝ → ℝ) (D : ℝ) (hD : 0 < D)
    (J n k : ℕ) (hJk : J ≤ k) (hkn : k ≤ n)
    (hF : ∀ x ∈ Icc 0 Real.pi, HasDerivAt F (dF x) x)
    (hdF : ∀ x ∈ Icc 0 Real.pi, D ≤ dF x)
    (hF0 : F 0 < J*Real.pi-Real.pi/4) (hFpi : F Real.pi = (n+1)*Real.pi) :
    ∃ a b : ℝ, a ∈ Ioo 0 Real.pi ∧ b ∈ Ioo 0 Real.pi ∧ a < b ∧
      F a = k*Real.pi-Real.pi/4 ∧ F b = k*Real.pi+Real.pi/4 := by
  have hc : ContinuousOn F (Icc 0 Real.pi) :=
    fun x hx ↦ (hF x hx).continuousAt.continuousWithinAt
  have hm : StrictMonoOn F (Icc 0 Real.pi) := strictMonoOn_of_deriv_pos (convex_Icc _ _) hc
    (fun x hx ↦ by rw [(hF x (interior_subset hx)).deriv]; exact hD.trans_le (hdF x (interior_subset hx)))
  have hJk' : (J : ℝ) ≤ k := by exact_mod_cast hJk
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have htarget0 : F 0 < k*Real.pi-Real.pi/4 := by nlinarith [Real.pi_pos]
  have htargetpi : k*Real.pi+Real.pi/4 < F Real.pi := by rw [hFpi]; nlinarith [Real.pi_pos]
  have htargets : k*Real.pi-Real.pi/4 < k*Real.pi+Real.pi/4 := by linarith [Real.pi_pos]
  obtain ⟨a, ha, hFa⟩ := intermediate_value_Icc (le_of_lt Real.pi_pos) hc
    ⟨le_of_lt htarget0, le_of_lt (htargets.trans htargetpi)⟩
  obtain ⟨b, hb, hFb⟩ := intermediate_value_Icc (le_of_lt Real.pi_pos) hc
    ⟨le_of_lt (htarget0.trans htargets), le_of_lt htargetpi⟩
  have ha0 : 0 < a := (hm.lt_iff_lt ⟨le_refl _, le_of_lt Real.pi_pos⟩ ha).mp (by rwa [hFa])
  have hbpi : b < Real.pi := (hm.lt_iff_lt hb ⟨le_of_lt Real.pi_pos, le_refl _⟩).mp (by rwa [hFb])
  have hab : a < b := (hm.lt_iff_lt ha hb).mp (by rwa [hFa, hFb])
  exact ⟨a, b, ⟨ha0, hab.trans hbpi⟩, ⟨ha0.trans hab, hbpi⟩, hab, hFa, hFb⟩

/-- There is exactly one simple root in each full tail phase cell. The
uniqueness conclusion ranges over the entire spectral interval `(0,pi)`. -/
theorem phase_tail_cell_root (F E dF dE : ℝ → ℝ) (D : ℝ) (hD : 0 < D)
    (J n k : ℕ) (hJk : J ≤ k) (hkn : k ≤ n)
    (hF : ∀ x ∈ Icc 0 Real.pi, HasDerivAt F (dF x) x)
    (hE : ∀ x ∈ Ioo 0 Real.pi, HasDerivAt E (dE x) x)
    (hdF : ∀ x ∈ Icc 0 Real.pi, D ≤ dF x)
    (hF0 : F 0 < J*Real.pi-Real.pi/4) (hFpi : F Real.pi = (n+1)*Real.pi)
    (hsmall : ∀ x ∈ Ioo 0 Real.pi, J*Real.pi-Real.pi/4 ≤ F x →
      |E x| ≤ (1 : ℝ)/4 ∧ |dE x| ≤ D/4) :
    ∃ x : ℝ, x ∈ Ioo 0 Real.pi ∧ |F x-k*Real.pi| ≤ Real.pi/4 ∧
      Real.sin (F x)+E x = 0 ∧ deriv (fun t ↦ Real.sin (F t)+E t) x ≠ 0 ∧
      ∀ y ∈ Ioo 0 Real.pi, |F y-k*Real.pi| ≤ Real.pi/4 →
        Real.sin (F y)+E y = 0 → y = x := by
  obtain ⟨a, b, ha, hb, hab, hFa, hFb⟩ :=
    phase_cell_endpoints F dF D hD J n k hJk hkn hF hdF hF0 hFpi
  have hc : ContinuousOn F (Icc 0 Real.pi) :=
    fun x hx ↦ (hF x hx).continuousAt.continuousWithinAt
  have hm : StrictMonoOn F (Icc 0 Real.pi) := strictMonoOn_of_deriv_pos (convex_Icc _ _) hc
    (fun x hx ↦ by rw [(hF x (interior_subset hx)).deriv]; exact hD.trans_le (hdF x (interior_subset hx)))
  have hac : a ∈ Icc 0 Real.pi := ⟨le_of_lt ha.1, le_of_lt ha.2⟩
  have hbc : b ∈ Icc 0 Real.pi := ⟨le_of_lt hb.1, le_of_lt hb.2⟩
  have hsub (x : ℝ) (hx : x ∈ Icc a b) : x ∈ Icc 0 Real.pi :=
    ⟨hac.1.trans hx.1, hx.2.trans hbc.2⟩
  have hsubo (x : ℝ) (hx : x ∈ Icc a b) : x ∈ Ioo 0 Real.pi :=
    ⟨ha.1.trans_le hx.1, hx.2.trans_lt hb.2⟩
  have hcell (x : ℝ) (hx : x ∈ Icc a b) : |F x-k*Real.pi| ≤ Real.pi/4 := by
    have hl := hm.monotoneOn hac (hsub x hx) hx.1
    have hu := hm.monotoneOn (hsub x hx) hbc hx.2
    rw [hFa] at hl
    rw [hFb] at hu
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have htail (x : ℝ) (hx : x ∈ Icc a b) : J*Real.pi-Real.pi/4 ≤ F x := by
    have hl := hm.monotoneOn hac (hsub x hx) hx.1
    rw [hFa] at hl
    have hJk' : (J : ℝ) ≤ k := by exact_mod_cast hJk
    nlinarith [Real.pi_pos]
  let s : ℝ := (-1)^k
  let u : ℝ → ℝ := fun x ↦ F x-k*Real.pi
  let e : ℝ → ℝ := fun x ↦ s*E x
  let de : ℝ → ℝ := fun x ↦ s*dE x
  let G : ℝ → ℝ := fun x ↦ Real.sin (u x)+e x
  have hs : |s| = 1 := by simp [s, abs_pow]
  have hs0 : s ≠ 0 := by simp [s]
  have hlocalF (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt u (dF x) x :=
    (hF x (hsub x hx)).sub_const _
  have hlocalE (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt e (de x) x :=
    (hE x (hsubo x hx)).const_mul s
  have hlocaldE (x : ℝ) (hx : x ∈ Icc a b) : |de x| ≤ D/4 := by
    simpa only [de, abs_mul, hs, one_mul] using (hsmall x (hsubo x hx) (htail x hx)).2
  have hlocale (x : ℝ) (hx : x ∈ Icc a b) : |e x| ≤ (1 : ℝ)/4 := by
    simpa only [e, abs_mul, hs, one_mul] using (hsmall x (hsubo x hx) (htail x hx)).1
  have hloc := phase_cell_unique_zero u e dF de a b D hab hD
    (by dsimp [u]; rw [hFa]; ring) (by dsimp [u]; rw [hFb]; ring)
    hcell hlocalF hlocalE (fun x hx ↦ hdF x (hsub x hx)) hlocaldE hlocale
  obtain ⟨x, hx, _⟩ := hloc.1
  have hxc : x ∈ Icc a b := ⟨le_of_lt hx.1.1, le_of_lt hx.1.2⟩
  have hG (t : ℝ) : G t = s*(Real.sin (F t)+E t) := by
    dsimp [G, u, e, s]
    rw [Real.sin_sub_nat_mul_pi]
    ring
  have hxzero : Real.sin (F x)+E x = 0 := by
    have hh : G x = 0 := hx.2
    rw [hG] at hh
    exact (mul_eq_zero.mp hh).resolve_left hs0
  have hDx : HasDerivAt (fun t ↦ Real.sin (F t)+E t)
      (Real.cos (F x)*dF x+dE x) x :=
    (hF x (hsub x hxc)).sin.add (hE x (hsubo x hxc))
  have hDG : HasDerivAt G (s*(Real.cos (F x)*dF x+dE x)) x := by
    rw [funext hG]
    exact hDx.const_mul s
  have hxder : deriv (fun t ↦ Real.sin (F t)+E t) x ≠ 0 := by
    intro hz
    have hgpos : 0 < deriv G x := hloc.2 x hxc
    rw [hDG.deriv, ← hDx.deriv, hz, mul_zero] at hgpos
    exact (lt_irrefl 0) hgpos
  refine ⟨x, ⟨ha.1.trans hx.1.1, hx.1.2.trans hb.2⟩, hcell x hxc, hxzero, hxder, ?_⟩
  intro y hy hycell hyzero
  have hyc : y ∈ Icc 0 Real.pi := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  have hyab : y ∈ Icc a b := by
    constructor
    · apply (hm.le_iff_le hac hyc).mp
      rw [hFa]
      have hh := (abs_le.mp hycell).1
      linarith
    · apply (hm.le_iff_le hyc hbc).mp
      rw [hFb]
      have hh := (abs_le.mp hycell).2
      linarith
  have hGc : ContinuousOn G (Icc a b) := fun z hz ↦
    ((hlocalF z hz).sin.add (hlocalE z hz)).continuousAt.continuousWithinAt
  have hGmono : StrictMonoOn G (Icc a b) := strictMonoOn_of_deriv_pos (convex_Icc _ _) hGc
    (fun z hz ↦ hloc.2 z (interior_subset hz))
  apply hGmono.injOn hyab hxc
  rw [hG, hG, hxzero, hyzero]

end MF21Phase

#print axioms MF21Phase.phase_cell_endpoints
#print axioms MF21Phase.phase_tail_cell_root
