import MF21.BulkPhase
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Order.Compact

noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace MF21Bulk
set_option backward.isDefEq.respectTransparency false

/-- A compactness version of the negative endpoint-derivative criterion
for exponential decay. The proof uses the continuous extended slope. -/
theorem exists_exp_bound_of_deriv_neg (f : ℝ → ℝ) (b d : ℝ) (hb : 0 ≤ b)
    (hc : ContinuousOn f (Icc 0 b)) (hzero : f 0 = 1)
    (hd : HasDerivAt f d 0) (hdneg : d < 0)
    (hlt : ∀ x ∈ Ioc 0 b, f x < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Icc 0 b, f x ≤ Real.exp (-c * x) := by
  have hcont : ContinuousOn (dslope f 0) (Icc 0 b) := by
    intro x hx
    by_cases he : x = 0
    · subst x
      exact (continuousAt_dslope_same.mpr hd.differentiableAt).continuousWithinAt
    · exact (continuousWithinAt_dslope_of_ne he).mpr (hc x hx)
  have hneg : ∀ x ∈ Icc 0 b, dslope f 0 x < 0 := by
    intro x hx
    by_cases he : x = 0
    · simpa [he, dslope_same, hd.deriv] using hdneg
    · have hxp : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm he)
      have heq := sub_smul_dslope f 0 x
      simp only [sub_zero, smul_eq_mul, hzero] at heq
      have hfx := hlt x ⟨hxp, hx.2⟩
      nlinarith
  obtain ⟨a, ha, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, hb⟩ hcont
  refine ⟨-dslope f 0 a, neg_pos.mpr (hneg a ha), ?_⟩
  intro x hx
  have hs := hmax hx
  have heq := sub_smul_dslope f 0 x
  simp only [sub_zero, smul_eq_mul, hzero] at heq
  have hh := mul_le_mul_of_nonneg_left hs hx.1
  have hexp := Real.add_one_le_exp (dslope f 0 a * x)
  simp only [neg_neg]
  nlinarith

theorem halfSine_hasDerivAt_zero :
    HasDerivAt (fun theta : ℝ => 2 * Real.sin (theta / 2)) 1 0 := by
  convert! (((hasDerivAt_id (0 : ℝ)).div_const 2).sin).const_mul 2 using 1 <;> norm_num

/-- A genuine smooth extension at zero of the angle-parametrized stable
root, which agrees with that root throughout the positive half-line.
Smoothness away from zero is needed only where the spectral base is positive. -/
theorem angleRoot_extension (omega kappa : ℂ)
    (homega : ‖omega‖ = 1) (hne : omega ≠ 1)
    (hk : kappa ^ 2 = -omega) (hkr : 0 < kappa.re) :
    ∃ F : ℝ → ℂ, F 0 = 1 ∧ ContDiffAt ℝ ∞ F 0 ∧ HasDerivAt F (-kappa) 0 ∧
      (∀ theta > 0, F theta = stableRoot omega (spectralBase theta)) ∧
      (∀ theta > 0, 0 < spectralBase theta → ContDiffAt ℝ ∞ F theta) := by
  obtain ⟨R, hR0, hRc, hRd, hRe⟩ :=
    stableRoot_endpoint_extension omega kappa homega hne hk hkr
  let T : ℝ → ℝ := fun theta => 2 * Real.sin (theta / 2)
  let G : ℝ → ℂ := fun theta => R (T theta)
  have hT0 : T 0 = 0 := by simp [T]
  have hTc : ContDiffAt ℝ ∞ T 0 := by dsimp [T]; fun_prop
  have hGc : ContDiffAt ℝ ∞ G 0 := by
    apply ContDiffAt.comp (f := T) (g := R) 0 _ hTc
    simpa [hT0] using hRc
  have hGd : HasDerivAt G (-kappa) 0 := by
    have hr : HasDerivAt R (-kappa) (T 0) := by simpa [hT0] using hRd
    have hTd : HasDerivAt T 1 0 := halfSine_hasDerivAt_zero
    simpa [G] using! hr.scomp 0 hTd
  have hGe : ∀ᶠ theta : ℝ in 𝓝[>] 0,
      G theta = stableRoot omega (spectralBase theta) :=
    halfSine_tendsto_pos.eventually hRe
  let F : ℝ → ℂ := fun theta =>
    if theta ≤ 0 then G theta else stableRoot omega (spectralBase theta)
  have hFG : F =ᶠ[𝓝 0] G := by
    rw [eventually_nhdsWithin_iff] at hGe
    filter_upwards [hGe] with theta he
    dsimp [F]
    split_ifs with ht
    · rfl
    · exact (he (lt_of_not_ge ht)).symm
  refine ⟨F, ?_, hGc.congr_of_eventuallyEq hFG,
    hGd.congr_of_eventuallyEq hFG, ?_, ?_⟩
  · simp [F, G, hT0, hR0]
  · intro theta ht
    exact if_neg (not_le_of_gt ht)
  · intro theta ht hs
    have hc := (stableRoot_contDiffAt omega (spectralBase theta) hs homega hne).comp
      theta spectralBase_contDiff.contDiffAt
    apply hc.congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds ht] with t htp
    exact if_neg (not_le_of_gt htp)

/-- The uniform exponential bound for the actual stable branch on the
whole positive angle interval, with the endpoint understood as one. -/
theorem stableRoot_angle_exp_bound (omega kappa : ℂ)
    (homega : ‖omega‖ = 1) (hne : omega ≠ 1)
    (hk : kappa ^ 2 = -omega) (hkr : 0 < kappa.re) :
    ∃ c : ℝ, 0 < c ∧ ∀ theta ∈ Ioc 0 Real.pi,
      ‖stableRoot omega (spectralBase theta)‖ ≤ Real.exp (-c * theta) := by
  obtain ⟨F, hF0, hFc0, hFd, hFe, hFc⟩ :=
    angleRoot_extension omega kappa homega hne hk hkr
  have hbase (theta : ℝ) (ht : theta ∈ Ioc 0 Real.pi) : 0 < spectralBase theta := by
    by_cases hp : theta = Real.pi
    · rw [hp, spectralBase_eq]; norm_num
    · exact spectralBase_pos theta ht.1 (lt_of_le_of_ne ht.2 hp)
  have hcont : ContinuousOn F (Icc 0 Real.pi) := by
    intro theta ht
    by_cases he : theta = 0
    · subst theta
      exact hFc0.continuousAt.continuousWithinAt
    · have htp := lt_of_le_of_ne ht.1 (Ne.symm he)
      exact (hFc theta htp (hbase theta ⟨htp, ht.2⟩)).continuousAt.continuousWithinAt
  let f : ℝ → ℝ := fun theta => Complex.normSq (F theta)
  have hfcont : ContinuousOn f (Icc 0 Real.pi) := by
    exact Complex.continuous_normSq.comp_continuousOn hcont
  have hfzero : f 0 = 1 := by simp [f, hF0]
  have hfre : HasDerivAt (fun theta => (F theta).re) (-kappa.re) 0 := by
    simpa using! Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hFd
  have hfim : HasDerivAt (fun theta => (F theta).im) (-kappa.im) 0 := by
    simpa using! Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hFd
  have hfd : HasDerivAt f (-2 * kappa.re) 0 := by
    have hh := (hfre.pow 2).add (hfim.pow 2)
    simpa [f, Complex.normSq_apply, hF0, pow_two] using! hh
  have hflt : ∀ theta ∈ Ioc 0 Real.pi, f theta < 1 := by
    intro theta ht
    have hn := (stableRoot_spec omega (spectralBase theta) (hbase theta ht) homega hne).2.1
    dsimp only [f]
    rw [hFe theta ht.1, ← Complex.sq_norm]
    nlinarith [norm_nonneg (stableRoot omega (spectralBase theta))]
  obtain ⟨c, hc, hbound⟩ := exists_exp_bound_of_deriv_neg f Real.pi (-2 * kappa.re)
    Real.pi_pos.le hfcont hfzero hfd (by linarith) hflt
  refine ⟨c / 2, by positivity, ?_⟩
  intro theta ht
  have hh := hbound theta ⟨ht.1.le, ht.2⟩
  dsimp only [f] at hh
  rw [hFe theta ht.1, ← Complex.sq_norm] at hh
  have he : Real.exp (-c * theta) = (Real.exp (-(c / 2) * theta)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [he] at hh
  nlinarith [Real.exp_pos (-(c / 2) * theta), norm_nonneg (stableRoot omega (spectralBase theta))]

theorem stableRoot_angle_logDeriv_bound (omega kappa : ℂ)
    (homega : ‖omega‖ = 1) (hne : omega ≠ 1)
    (hk : kappa ^ 2 = -omega) (hkr : 0 < kappa.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ theta ∈ Ioc 0 Real.pi,
      ‖deriv (fun t => stableRoot omega (spectralBase t)) theta /
        stableRoot omega (spectralBase theta)‖ ≤ C := by
  obtain ⟨F, hF0, hFc0, _, hFe, hFc⟩ :=
    angleRoot_extension omega kappa homega hne hk hkr
  have hbase (theta : ℝ) (ht : theta ∈ Ioc 0 Real.pi) : 0 < spectralBase theta := by
    by_cases hp : theta = Real.pi
    · rw [hp, spectralBase_eq]; norm_num
    · exact spectralBase_pos theta ht.1 (lt_of_le_of_ne ht.2 hp)
  have hcall (theta : ℝ) (ht : theta ∈ Icc 0 Real.pi) : ContDiffAt ℝ ∞ F theta := by
    by_cases he : theta = 0
    · simpa [he] using hFc0
    · have htp := lt_of_le_of_ne ht.1 (Ne.symm he)
      exact hFc theta htp (hbase theta ⟨htp, ht.2⟩)
  have hnz (theta : ℝ) (ht : theta ∈ Icc 0 Real.pi) : F theta ≠ 0 := by
    by_cases he : theta = 0
    · simp [he, hF0]
    · have htp := lt_of_le_of_ne ht.1 (Ne.symm he)
      rw [hFe theta htp]
      exact (stableRoot_spec omega (spectralBase theta)
        (hbase theta ⟨htp, ht.2⟩) homega hne).1
  have hc : ContinuousOn (fun theta => ‖deriv F theta / F theta‖) (Icc 0 Real.pi) := by
    intro theta ht
    have hd : ContDiffAt ℝ 0 (deriv F) theta := (hcall theta ht).derivWithin (by simp)
    exact (hd.continuousAt.div (hcall theta ht).continuousAt (hnz theta ht)).norm.continuousWithinAt
  obtain ⟨a, ha, hamax⟩ := isCompact_Icc.exists_isMaxOn
    ⟨0, le_rfl, Real.pi_pos.le⟩ hc
  refine ⟨‖deriv F a / F a‖, norm_nonneg _, ?_⟩
  intro theta ht
  have heq : (fun t => stableRoot omega (spectralBase t)) =ᶠ[𝓝 theta] F := by
    filter_upwards [lt_mem_nhds ht.1] with t htp
    exact (hFe t htp).symm
  rw [heq.deriv_eq, ← hFe theta ht.1]
  exact hamax ⟨ht.1.le, ht.2⟩

end MF21Bulk

#print axioms MF21Bulk.exists_exp_bound_of_deriv_neg
#print axioms MF21Bulk.angleRoot_extension
#print axioms MF21Bulk.stableRoot_angle_exp_bound
#print axioms MF21Bulk.stableRoot_angle_logDeriv_bound
