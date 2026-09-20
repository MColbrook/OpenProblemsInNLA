import MF21.BulkDecay
import Mathlib.LinearAlgebra.Vandermonde

noncomputable section
open Filter Set
open scoped Topology ContDiff BigOperators
namespace MF21Bulk
set_option backward.isDefEq.respectTransparency false

def halfSine (theta : ℝ) : ℝ := 2 * Real.sin (theta / 2)

@[fun_prop] theorem halfSine_contDiff : ContDiff ℝ ∞ halfSine := by
  change ContDiff ℝ ∞ (fun theta => 2 * Real.sin (theta / 2))
  fun_prop

theorem halfSine_pos (theta : ℝ) (ht : theta ∈ Ioc 0 Real.pi) : 0 < halfSine theta := by
  apply mul_pos (by norm_num)
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])

theorem spectralBase_pos_of_mem (theta : ℝ) (ht : theta ∈ Ioc 0 Real.pi) :
    0 < spectralBase theta := sq_pos_of_pos (halfSine_pos theta ht)

/-- A smooth factor U(theta) with r(theta)=1+t(theta)U(theta) on the
positive angle interval. This is the factor needed in row normalization. -/
theorem stable_slope_extension (omega kappa : ℂ)
    (homega : ‖omega‖ = 1) (hne : omega ≠ 1)
    (hk : kappa ^ 2 = -omega) (hkr : 0 < kappa.re) :
    ∃ U : ℝ → ℂ, U 0 = -kappa ∧
      (∀ theta ∈ Icc 0 Real.pi, ContDiffAt ℝ ∞ U theta) ∧
      ∀ theta ∈ Ioc 0 Real.pi,
        stableRoot omega (spectralBase theta) = 1 + (halfSine theta : ℂ) * U theta := by
  obtain ⟨V, R, hV0, hVc, hRform, _, _, _, hRe⟩ :=
    stableRoot_endpoint_factorization omega kappa homega hne hk hkr
  let G : ℝ → ℂ := fun theta => V (halfSine theta)
  let U : ℝ → ℂ := fun theta => if theta ≤ 0 then G theta else
    (stableRoot omega (spectralBase theta) - 1) / (halfSine theta : ℂ)
  have hGe : ∀ᶠ theta : ℝ in 𝓝[>] 0,
      (stableRoot omega (spectralBase theta) - 1) / (halfSine theta : ℂ) = G theta := by
    filter_upwards [halfSine_tendsto_pos.eventually hRe,
      halfSine_tendsto_pos.eventually self_mem_nhdsWithin] with theta he ht
    change 0 < halfSine theta at ht
    have he' : stableRoot omega (spectralBase theta) =
        1 + (halfSine theta : ℂ) * G theta := by
      change R (halfSine theta) = stableRoot omega (spectralBase theta) at he
      rw [← he, hRform]
    rw [he']
    have htn : (halfSine theta : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
    field_simp [htn]
    ring
  have hGc : ContDiffAt ℝ ∞ G 0 := by
    have hc : ContDiffAt ℝ ∞ V (halfSine 0) := by simpa [halfSine] using hVc
    exact hc.comp 0 halfSine_contDiff.contDiffAt
  have hUG : U =ᶠ[𝓝 0] G := by
    rw [eventually_nhdsWithin_iff] at hGe
    filter_upwards [hGe] with theta he
    dsimp [U]
    split_ifs with ht
    · rfl
    · exact he (lt_of_not_ge ht)
  refine ⟨U, by simp [U, G, halfSine, hV0], ?_, ?_⟩
  · intro theta ht
    by_cases he : theta = 0
    · subst theta
      exact hGc.congr_of_eventuallyEq hUG
    · have htp := lt_of_le_of_ne ht.1 (Ne.symm he)
      have hs := spectralBase_pos_of_mem theta ⟨htp, ht.2⟩
      have hc : ContDiffAt ℝ ∞ (fun x => stableRoot omega (spectralBase x) - 1) theta :=
        ((stableRoot_contDiffAt omega (spectralBase theta) hs homega hne).comp
        theta spectralBase_contDiff.contDiffAt).sub contDiffAt_const
      have htcomplex : ContDiffAt ℝ ∞ (fun x => (halfSine x : ℂ)) theta :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp theta halfSine_contDiff.contDiffAt
      have htn : (halfSine theta : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (halfSine_pos theta ⟨htp, ht.2⟩))
      have hquot : ContDiffAt ℝ ∞ (fun x =>
          (stableRoot omega (spectralBase x) - 1) / (halfSine x : ℂ)) theta := by
        simpa only [div_eq_mul_inv] using! hc.mul (htcomplex.inv htn)
      apply hquot.congr_of_eventuallyEq
      filter_upwards [lt_mem_nhds htp] with x hx
      exact if_neg (not_le_of_gt hx)
  · intro theta ht
    simp only [U, if_neg (not_le_of_gt ht.1)]
    have htn : (halfSine theta : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (halfSine_pos theta ht)
    field_simp
    ring

theorem unitRoot_factor (theta : ℝ) :
    unitRoot theta = 1 + (halfSine theta : ℂ) * (Complex.I * unitRoot (theta / 2)) := by
  have he := one_sub_unitRoot_neg (-theta)
  simp only [neg_neg, neg_div, Real.sin_neg, mul_neg, Complex.ofReal_neg] at he
  dsimp [halfSine]
  linear_combination -he

theorem baseRoot_spec_of_pos (m : ℕ) (hm : 0 < m) (theta : ℝ)
    (hs : 0 < spectralBase theta) (j : Fin m) :
    baseRoot m theta j ≠ 0 ∧
      2 - baseRoot m theta j - (baseRoot m theta j)⁻¹ =
        omega m j * (spectralBase theta : ℂ) := by
  by_cases hj : j.val = 0
  · simp only [baseRoot, omega, hj, if_true, pow_zero, one_mul]
    exact ⟨unitRoot_ne_zero theta, unitRoot_characteristic theta⟩
  · obtain ⟨hn, _, he⟩ := stableRoot_spec (omega m j) (spectralBase theta)
      hs (omega_norm m j) (omega_ne_one m hm j hj)
    simpa only [baseRoot, if_neg hj] using And.intro hn he

theorem baseRoot_injective_of_pos (m : ℕ) (hm : 0 < m) (theta : ℝ)
    (hs : 0 < spectralBase theta) : Function.Injective (baseRoot m theta) := by
  intro i j hij
  apply omega_injective m hm
  have hi := (baseRoot_spec_of_pos m hm theta hs i).2
  have hj := (baseRoot_spec_of_pos m hm theta hs j).2
  rw [hij] at hi
  exact mul_right_cancel₀ (by exact_mod_cast ne_of_gt hs) (hi.symm.trans hj)

def endpointSlope (m : ℕ) (j : Fin m) : ℂ :=
  if j.val = 0 then Complex.I else -kappa m j

theorem endpointSlope_sq (m : ℕ) (j : Fin m) :
    endpointSlope m j ^ 2 = -omega m j := by
  by_cases hj : j.val = 0
  · simp [endpointSlope, hj, omega, Complex.I_sq]
  · simpa [endpointSlope, hj] using kappa_sq m j

theorem endpointSlope_injective (m : ℕ) (hm : 0 < m) :
    Function.Injective (endpointSlope m) := by
  intro i j he
  apply omega_injective m hm
  have hh := congrArg (fun z : ℂ => z ^ 2) he
  rw [endpointSlope_sq, endpointSlope_sq] at hh
  exact neg_injective hh

/-- The m base-root slopes are smooth on the whole closed interval,
including both endpoints, and remain pairwise distinct there. -/
theorem base_slopes_exist (m : ℕ) (hm : 0 < m) :
    ∃ U : Fin m → ℝ → ℂ,
      (∀ j, U j 0 = endpointSlope m j) ∧
      (∀ j theta, theta ∈ Icc 0 Real.pi → ContDiffAt ℝ ∞ (U j) theta) ∧
      (∀ j theta, theta ∈ Ioc 0 Real.pi →
        baseRoot m theta j = 1 + (halfSine theta : ℂ) * U j theta) ∧
      (∀ theta ∈ Icc 0 Real.pi, Function.Injective (fun j => U j theta)) := by
  have heach (j : Fin m) : ∃ U : ℝ → ℂ, U 0 = endpointSlope m j ∧
      (∀ theta ∈ Icc 0 Real.pi, ContDiffAt ℝ ∞ U theta) ∧
      ∀ theta ∈ Ioc 0 Real.pi,
        baseRoot m theta j = 1 + (halfSine theta : ℂ) * U theta := by
    by_cases hj : j.val = 0
    · refine ⟨fun theta => Complex.I * unitRoot (theta / 2), ?_, ?_, ?_⟩
      · simp [endpointSlope, hj, unitRoot]
      · intro theta _
        exact contDiffAt_const.mul
          (unitRoot_contDiff.contDiffAt.comp theta (by fun_prop))
      · intro theta _
        simpa only [baseRoot, if_pos hj] using unitRoot_factor theta
    · obtain ⟨U, hU0, hUc, hUe⟩ := stable_slope_extension (omega m j) (kappa m j)
        (omega_norm m j) (omega_ne_one m hm j hj) (kappa_sq m j) (kappa_re_pos m hm j hj)
      exact ⟨U, by simpa [endpointSlope, hj] using hU0, hUc,
        fun theta ht => by simpa only [baseRoot, if_neg hj] using hUe theta ht⟩
  choose U hU0 hUc hUe using heach
  refine ⟨U, hU0, hUc, hUe, ?_⟩
  intro theta ht i j hij
  change U i theta = U j theta at hij
  by_cases he : theta = 0
  · subst theta
    simp only [hU0] at hij
    exact endpointSlope_injective m hm hij
  · have htp := lt_of_le_of_ne ht.1 (Ne.symm he)
    apply baseRoot_injective_of_pos m hm theta (spectralBase_pos_of_mem theta ⟨htp, ht.2⟩)
    rw [hUe i theta ⟨htp, ht.2⟩, hUe j theta ⟨htp, ht.2⟩, hij]

def blockRootFamily (m : ℕ) (theta : ℝ) : Fin m ⊕ Fin m → ℂ :=
  Sum.elim (baseRoot m theta) (fun j => (baseRoot m theta j)⁻¹)

def slopeNormalizer (m : ℕ) (U : (Fin m ⊕ Fin m) → ℝ → ℂ) (theta : ℝ) : ℂ :=
  (Matrix.vandermonde (fun j => U (Sum.inl j) theta)).det *
    (Matrix.vandermonde (fun j => U (Sum.inr j) theta)).det

/-- Smooth slopes for all roots and a nonvanishing smooth leading
Vandermonde coefficient, with no removable quotient assumption. -/
theorem block_slopes_exist (m : ℕ) (hm : 0 < m) :
    ∃ U : (Fin m ⊕ Fin m) → ℝ → ℂ,
      (∀ j, U (Sum.inl j) 0 = endpointSlope m j ∧
        U (Sum.inr j) 0 = -endpointSlope m j) ∧
      (∀ j theta, theta ∈ Icc 0 Real.pi → ContDiffAt ℝ ∞ (U j) theta) ∧
      (∀ j theta, theta ∈ Ioc 0 Real.pi →
        blockRootFamily m theta j = 1 + (halfSine theta : ℂ) * U j theta) ∧
      (∀ theta ∈ Icc 0 Real.pi, slopeNormalizer m U theta ≠ 0) ∧
      (∀ theta ∈ Icc 0 Real.pi, ContDiffAt ℝ ∞ (slopeNormalizer m U) theta) := by
  obtain ⟨V, hV0, hVc, hVe, hVi⟩ := base_slopes_exist m hm
  let R : Fin m → ℝ → ℂ := fun j theta => 1 + (halfSine theta : ℂ) * V j theta
  let U : (Fin m ⊕ Fin m) → ℝ → ℂ :=
    Sum.elim V (fun j theta => -V j theta / R j theta)
  have hRn (j : Fin m) (theta : ℝ) (ht : theta ∈ Icc 0 Real.pi) : R j theta ≠ 0 := by
    by_cases he : theta = 0
    · simp [R, he, halfSine]
    · have htp := lt_of_le_of_ne ht.1 (Ne.symm he)
      change 1 + _ * _ ≠ 0
      rw [← hVe j theta ⟨htp, ht.2⟩]
      exact (baseRoot_spec_of_pos m hm theta (spectralBase_pos_of_mem theta ⟨htp, ht.2⟩) j).1
  have hUc (j : Fin m ⊕ Fin m) (theta : ℝ) (ht : theta ∈ Icc 0 Real.pi) :
      ContDiffAt ℝ ∞ (U j) theta := by
    cases j with
    | inl j => exact hVc j theta ht
    | inr j =>
      change ContDiffAt ℝ ∞ (fun x => -V j x / R j x) theta
      have htc : ContDiffAt ℝ ∞ (fun x => (halfSine x : ℂ)) theta :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp theta halfSine_contDiff.contDiffAt
      have hRc : ContDiffAt ℝ ∞ (R j) theta :=
        contDiffAt_const.add (htc.mul (hVc j theta ht))
      simpa only [div_eq_mul_inv] using! (hVc j theta ht).neg.mul (hRc.inv (hRn j theta ht))
  have hUe (j : Fin m ⊕ Fin m) (theta : ℝ) (ht : theta ∈ Ioc 0 Real.pi) :
      blockRootFamily m theta j = 1 + (halfSine theta : ℂ) * U j theta := by
    cases j with
    | inl j => exact hVe j theta ht
    | inr j =>
      change (baseRoot m theta j)⁻¹ = 1 + (halfSine theta : ℂ) * (-V j theta / R j theta)
      rw [hVe j theta ht]
      have hn := hRn j theta ⟨ht.1.le, ht.2⟩
      dsimp only [R] at *
      field_simp
      ring
  have hright (theta : ℝ) (ht : theta ∈ Icc 0 Real.pi) :
      Function.Injective (fun j => U (Sum.inr j) theta) := by
    intro i j hij
    change U (Sum.inr i) theta = U (Sum.inr j) theta at hij
    by_cases he : theta = 0
    · subst theta
      simp only [U, Sum.elim_inr, R, halfSine, zero_div, Real.sin_zero, mul_zero,
        Complex.ofReal_zero, zero_mul, add_zero, div_one] at hij
      exact hVi 0 ht (neg_injective hij)
    · have htp := lt_of_le_of_ne ht.1 (Ne.symm he)
      apply baseRoot_injective_of_pos m hm theta (spectralBase_pos_of_mem theta ⟨htp, ht.2⟩)
      apply inv_injective
      change blockRootFamily m theta (Sum.inr i) = blockRootFamily m theta (Sum.inr j)
      rw [hUe _ theta ⟨htp, ht.2⟩, hUe _ theta ⟨htp, ht.2⟩, hij]
  refine ⟨U, ?_, hUc, hUe, ?_, ?_⟩
  · intro j
    simp [U, R, halfSine, hV0]
  · intro theta ht
    exact mul_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr (hVi theta ht))
      (Matrix.det_vandermonde_ne_zero_iff.mpr (hright theta ht))
  · intro theta ht
    change ContDiffAt ℝ ∞ (fun x =>
      (Matrix.vandermonde (fun j => U (Sum.inl j) x)).det *
        (Matrix.vandermonde (fun j => U (Sum.inr j) x)).det) theta
    simp only [Matrix.det_vandermonde]
    apply ContDiffAt.mul
    all_goals
      apply contDiffAt_prod
      intro j _
      apply contDiffAt_prod
      intro i _
      exact (hUc _ theta ht).sub (hUc _ theta ht)

end MF21Bulk

#print axioms MF21Bulk.stable_slope_extension
#print axioms MF21Bulk.base_slopes_exist
#print axioms MF21Bulk.block_slopes_exist
