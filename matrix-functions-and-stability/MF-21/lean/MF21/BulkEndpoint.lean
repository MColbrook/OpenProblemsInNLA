import MF21.BulkRoots

/-! Desingularization of the actual stable characteristic root at the
zero spectral endpoint. The change r = 1 + t u transforms its equation
into u² + omega t u + omega = 0; this equation has simple roots at t = 0. -/

noncomputable section
open Filter
open scoped Topology ContDiff
namespace MF21Bulk

theorem local_desingularized_root_analytic (omega u : ℂ)
    (hp : u ^ 2 + omega = 0) (hu : u ≠ 0) :
    ∃ U : ℂ → ℂ, U 0 = u ∧ ContDiffAt ℂ ω U 0 ∧
      ∀ᶠ t : ℂ in 𝓝 0, (U t) ^ 2 + omega * t * U t + omega = 0 := by
  let F : ℂ × ℂ → ℂ := fun p => p.2 ^ 2 + omega * p.1 * p.2 + omega
  have hc : ContDiffAt ℂ ω F (0, u) := by dsimp [F]; fun_prop
  have hd : HasDerivAt (fun z : ℂ => z ^ 2 + omega * 0 * z + omega)
      (2 * u) u := by
    simpa using ((hasDerivAt_id u).pow 2).add_const omega
  have hpartial : fderiv ℂ F (0, u) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ =
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (2 * u) := by
    have hcomp := (hc.differentiableAt (by simp)).hasFDerivAt.comp u
      ((hasFDerivAt_const (0 : ℂ) u).prodMk (hasFDerivAt_id u))
    have hpoly : HasFDerivAt (fun z : ℂ => z ^ 2 + omega * 0 * z + omega)
        (fderiv ℂ F (0, u) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ) u := by
      simpa [F, Function.comp_def, ContinuousLinearMap.inr] using hcomp
    exact hpoly.unique hd.hasFDerivAt
  have hinv : (fderiv ℂ F (0, u) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
    rw [hpartial]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ
      (Units.mk0 (2 * u) (mul_ne_zero (by norm_num) hu)), ?_⟩
    rfl
  let U := hc.implicitFunction (by simp) hinv
  refine ⟨U, hc.implicitFunction_apply_self (by simp) hinv,
    hc.contDiffAt_implicitFunction (by simp) hinv, ?_⟩
  filter_upwards [hc.eventually_apply_implicitFunction (by simp) hinv] with t ht
  simpa only [F, mul_zero, zero_mul, add_zero, hp] using ht

theorem local_desingularized_root (omega u : ℂ)
    (hp : u ^ 2 + omega = 0) (hu : u ≠ 0) :
    ∃ U : ℂ → ℂ, U 0 = u ∧ ContDiffAt ℂ ∞ U 0 ∧
      ∀ᶠ t : ℂ in 𝓝 0, (U t) ^ 2 + omega * t * U t + omega = 0 := by
  obtain ⟨U, h0, hc, he⟩ := local_desingularized_root_analytic omega u hp hu
  exact ⟨U, h0, hc.of_le (by simp), he⟩

theorem desingularized_polynomial (omega u t : ℂ)
    (hp : u ^ 2 + omega * t * u + omega = 0) :
    (1 + t * u) ^ 2 - (2 - omega * t ^ 2) * (1 + t * u) + 1 = 0 := by
  linear_combination t ^ 2 * hp

/-- A smooth continuation through zero of the uniquely defined stable root
at the squared spectral parameter. The equality is asserted on the
positive side, and the derivative is the characteristic decay constant. -/
theorem stableRoot_endpoint_factorization_analytic (omega kappa : ℂ)
    (homega : ‖omega‖ = 1) (hne : omega ≠ 1)
    (hk : kappa ^ 2 = -omega) (hkr : 0 < kappa.re) :
    ∃ U R : ℝ → ℂ, U 0 = -kappa ∧ ContDiffAt ℝ ω U 0 ∧
      (∀ t, R t = 1 + (t : ℂ) * U t) ∧
      R 0 = 1 ∧ ContDiffAt ℝ ω R 0 ∧
      HasDerivAt R (-kappa) 0 ∧
      ∀ᶠ t : ℝ in 𝓝[>] 0, R t = stableRoot omega (t ^ 2) := by
  have hkn : -kappa ≠ 0 := by
    intro he
    have hz : kappa = 0 := neg_eq_zero.mp he
    simp [hz] at hkr
  obtain ⟨U, hU0, hUc, hUe⟩ := local_desingularized_root_analytic omega (-kappa)
    (by rw [neg_sq, hk]; ring) hkn
  let Ur : ℝ → ℂ := fun t => U (t : ℂ)
  have hUr : ContDiffAt ℝ ω Ur 0 := by
    have hc : ContDiffAt ℝ ω U (Complex.ofRealCLM (0 : ℝ)) := hUc.restrict_scalars ℝ
    exact hc.comp (0 : ℝ) Complex.ofRealCLM.contDiff.contDiffAt
  have hUr0 : Ur 0 = -kappa := by simpa [Ur] using hU0
  let R : ℝ → ℂ := fun t => 1 + (t : ℂ) * Ur t
  have hR0 : R 0 = 1 := by simp [R]
  have hRc : ContDiffAt ℝ ω R 0 := by
    exact contDiffAt_const.add (Complex.ofRealCLM.contDiff.contDiffAt.mul hUr)
  have hRd : HasDerivAt R (-kappa) 0 := by
    have hd := Complex.ofRealCLM.hasFDerivAt.hasDerivAt.mul
      (hUr.differentiableAt (by simp)).hasDerivAt
    simpa [R, hUr0] using hd.const_add 1
  have hpoly : ∀ᶠ t : ℝ in 𝓝 0,
      (Ur t) ^ 2 + omega * t * Ur t + omega = 0 :=
    Complex.continuous_ofReal.continuousAt.tendsto.eventually hUe
  have hneg : ∀ᶠ t : ℝ in 𝓝 0,
      2 * (Ur t).re + t * Complex.normSq (Ur t) < 0 := by
    have hc : ContinuousAt
        (fun t : ℝ => 2 * (Ur t).re + t * Complex.normSq (Ur t)) 0 := by
      fun_prop
    have hzero : 2 * (Ur 0).re + (0 : ℝ) * Complex.normSq (Ur 0) < 0 := by
      simp only [hUr0, Complex.neg_re, zero_mul, add_zero]
      linarith
    exact hc.eventually (gt_mem_nhds hzero)
  refine ⟨Ur, R, hUr0, hUr, fun _ => rfl, hR0, hRc, hRd, ?_⟩
  filter_upwards [hpoly.filter_mono nhdsWithin_le_nhds,
    hneg.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with t hp hnt ht
  have htpos : 0 < t := ht
  have hpR : (R t) ^ 2 - (2 - omega * (t ^ 2 : ℝ)) * R t + 1 = 0 := by
    simpa only [R, Complex.ofReal_pow] using desingularized_polynomial omega (Ur t) t hp
  have hr : R t ≠ 0 := by intro hz; simp [hz] at hpR
  have hnorm : ‖R t‖ < 1 := by
    have hns : Complex.normSq (R t) =
        1 + t * (2 * (Ur t).re + t * Complex.normSq (Ur t)) := by
      simp [R, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
      ring
    have hh := mul_neg_of_pos_of_neg htpos hnt
    have hs := Complex.sq_norm (R t)
    rw [hns] at hs
    nlinarith [norm_nonneg (R t)]
  apply stableRoot_eq_of_spec omega (R t) (t ^ 2) (sq_pos_of_pos htpos)
    homega hne hr hnorm
  apply mul_right_cancel₀ hr
  field_simp
  linear_combination -hpR

theorem stableRoot_endpoint_factorization (omega kappa : ℂ)
    (homega : ‖omega‖ = 1) (hne : omega ≠ 1)
    (hk : kappa ^ 2 = -omega) (hkr : 0 < kappa.re) :
    ∃ U R : ℝ → ℂ, U 0 = -kappa ∧ ContDiffAt ℝ ∞ U 0 ∧
      (∀ t, R t = 1 + (t : ℂ) * U t) ∧
      R 0 = 1 ∧ ContDiffAt ℝ ∞ R 0 ∧ HasDerivAt R (-kappa) 0 ∧
      ∀ᶠ t : ℝ in 𝓝[>] 0, R t = stableRoot omega (t ^ 2) := by
  obtain ⟨U, R, hU0, hUc, hRf, hR0, hRc, hRd, hRe⟩ :=
    stableRoot_endpoint_factorization_analytic omega kappa homega hne hk hkr
  exact ⟨U, R, hU0, hUc.of_le (by simp), hRf, hR0, hRc.of_le (by simp), hRd, hRe⟩

theorem stableRoot_endpoint_extension (omega kappa : ℂ)
    (homega : ‖omega‖ = 1) (hne : omega ≠ 1)
    (hk : kappa ^ 2 = -omega) (hkr : 0 < kappa.re) :
    ∃ R : ℝ → ℂ, R 0 = 1 ∧ ContDiffAt ℝ ∞ R 0 ∧
      HasDerivAt R (-kappa) 0 ∧
      ∀ᶠ t : ℝ in 𝓝[>] 0, R t = stableRoot omega (t ^ 2) := by
  obtain ⟨U, R, _, _, _, hR⟩ :=
    stableRoot_endpoint_factorization omega kappa homega hne hk hkr
  exact ⟨R, hR⟩

end MF21Bulk

#print axioms MF21Bulk.local_desingularized_root
#print axioms MF21Bulk.stableRoot_endpoint_factorization_analytic
#print axioms MF21Bulk.stableRoot_endpoint_factorization
#print axioms MF21Bulk.stableRoot_endpoint_extension
