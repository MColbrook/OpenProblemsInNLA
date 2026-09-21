import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-!
The exact derivative/factorial coefficients and a uniform Taylor bound
for a jointly analytic real function of (x,h). Compactness bounds the
vertical derivative uniformly in x. The scalar Lagrange remainder is
then applied with either sign of h. See `IMPLICIT_TAYLOR_STATEMENTS.md`.
-/

set_option autoImplicit false
noncomputable section
open scoped Topology BigOperators

namespace MF21Restart

def verticalIteratedDeriv (F : ℝ × ℝ → ℝ) (k : ℕ) (p : ℝ × ℝ) : ℝ :=
  iteratedDeriv k (fun h : ℝ => F (p.1, h)) p.2

def parametricTaylorCoefficient (F : ℝ × ℝ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  iteratedDeriv k (fun h : ℝ => F (x, h)) 0 / (k.factorial : ℝ)

set_option backward.isDefEq.respectTransparency.types false in
/-- Actual iterated h-derivatives remain jointly analytic in (x,h). -/
theorem verticalIteratedDeriv_contDiffAt
    (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (hF : ContDiffAt ℝ ⊤ F p) (k : ℕ) :
    ContDiffAt ℝ ⊤ (verticalIteratedDeriv F k) p := by
  induction k with
  | zero =>
    have hzero : verticalIteratedDeriv F 0 = F := by
      funext q
      simp only [verticalIteratedDeriv, iteratedDeriv_zero]
    rw [hzero]
    exact hF
  | succ k ih =>
    have hjoint : ContDiffAt ℝ ⊤
        (Function.uncurry (fun q : ℝ × ℝ => fun t : ℝ =>
          verticalIteratedDeriv F k (q.1, t))) (p, p.2) :=
      ih.comp (p, p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hd : ContDiffAt ℝ ⊤
        (fun q : ℝ × ℝ =>
          fderiv ℝ (fun t : ℝ => verticalIteratedDeriv F k (q.1, t)) q.2) p :=
      hjoint.fderiv contDiffAt_snd (by simp)
    have he := hd.clm_apply
      (show ContDiffAt ℝ ⊤ (fun _ : ℝ × ℝ => (1 : ℝ)) p from contDiffAt_const)
    have hstep : verticalIteratedDeriv F (k + 1) =
        fun q : ℝ × ℝ =>
          (fderiv ℝ (fun t : ℝ => verticalIteratedDeriv F k (q.1, t)) q.2) 1 := by
      funext q
      change iteratedDeriv (k + 1) (fun h : ℝ => F (q.1, h)) q.2 =
        deriv (iteratedDeriv k (fun h : ℝ => F (q.1, h))) q.2
      rw [iteratedDeriv_succ]
    rw [hstep]
    exact he

/-- Regularity of the literal h-derivative/factorial coefficient. -/
theorem parametricTaylorCoefficient_contDiffAt
    (F : ℝ × ℝ → ℝ) (k : ℕ) (x : ℝ)
    (hF : ContDiffAt ℝ ⊤ F (x, 0)) :
    ContDiffAt ℝ ⊤ (parametricTaylorCoefficient F k) x := by
  have hd := verticalIteratedDeriv_contDiffAt F (x, 0) hF k
  have hc := hd.comp x (contDiffAt_id.prodMk contDiffAt_const)
  exact hc.div_const (k.factorial : ℝ)

/-- All Taylor orders use one neighborhood and the same derivative
coefficients. Only the remainder constant depends on the order. -/
theorem parametricTaylor_uniform_remainder
    (F : ℝ × ℝ → ℝ) (L r ε : ℝ) (hL : 0 ≤ L) (hr : 0 < r) (hε : 0 < ε)
    (hF : ∀ q ∈ Set.Ioo (-r / 2) (L + r / 2) ×ˢ Set.Ioo (-ε) ε,
      ContDiffAt ℝ ⊤ F q) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ ∀ p : ℕ, ∃ Cp : ℝ, 0 < Cp ∧
      ∀ x ∈ Set.Icc (0 : ℝ) L, ∀ h : ℝ, |h| ≤ δ →
        |F (x, h) - ∑ k ∈ Finset.range (p + 1), parametricTaylorCoefficient F k x * h ^ k| ≤
          Cp * |h| ^ (p + 1) := by
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : δ < ε := by dsimp [δ]; linarith
  let K : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) L ×ˢ Set.Icc (-δ) δ
  have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKsub : K ⊆ Set.Ioo (-r / 2) (L + r / 2) ×ˢ Set.Ioo (-ε) ε := by
    intro q hq
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith [hq.1.1, hq.1.2, hq.2.1, hq.2.2]
  refine ⟨δ, hδ, hδε, ?_⟩
  intro p
  have hc : ContinuousOn (verticalIteratedDeriv F (p + 1)) K := by
    intro q hq
    exact (verticalIteratedDeriv_contDiffAt F q (hF q (hKsub hq)) (p + 1)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hKcompact.exists_bound_of_continuousOn hc
  have hfact : (0 : ℝ) < ((p + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (p + 1)
  let Cp : ℝ := max M 1 / ((p + 1).factorial : ℝ)
  have hCp : 0 < Cp := div_pos (lt_of_lt_of_le zero_lt_one (le_max_right M 1)) hfact
  refine ⟨Cp, hCp, ?_⟩
  intro x hx h hh
  by_cases hzero : h = 0
  · subst h
    simp [Finset.sum_range_succ', parametricTaylorCoefficient]
  have hseg : Set.uIcc (0 : ℝ) h ⊆ Set.Icc (-δ) δ :=
    Set.uIcc_subset_Icc ⟨by linarith, hδ.le⟩ (abs_le.mp hh)
  let f : ℝ → ℝ := fun t => F (x, t)
  have hsection (t : ℝ) (ht : t ∈ Set.Icc (-δ) δ) : ContDiffAt ℝ ⊤ f t :=
    (hF (x, t) (hKsub ⟨hx, ht⟩)).comp t (contDiffAt_const.prodMk contDiffAt_id)
  have hfn : ContDiffOn ℝ (p + 1) f (Set.uIcc (0 : ℝ) h) := by
    intro t ht
    exact ((hsection t (hseg ht)).of_le le_top).contDiffWithinAt
  obtain ⟨t, ht, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (Ne.symm hzero) hfn
  have hpoly : taylorWithinEval f p (Set.uIcc (0 : ℝ) h) 0 h =
      ∑ k ∈ Finset.range (p + 1), parametricTaylorCoefficient F k x * h ^ k := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (Ne.symm hzero))
      ((hsection 0 ⟨by linarith, hδ.le⟩).of_le le_top) Set.left_mem_uIcc]
    simp only [sub_zero, smul_eq_mul, parametricTaylorCoefficient, f]
    ring
  have htK : (x, t) ∈ K := ⟨hx, hseg (Set.uIoo_subset_uIcc_self ht)⟩
  have hbound : |iteratedDeriv (p + 1) f t| ≤ max M 1 := by
    have hb : |iteratedDeriv (p + 1) f t| ≤ M := by
      simpa only [verticalIteratedDeriv, Real.norm_eq_abs, f] using hM (x, t) htK
    exact hb.trans (le_max_left M 1)
  change |f h - ∑ k ∈ Finset.range (p + 1), parametricTaylorCoefficient F k x * h ^ k| ≤
    Cp * |h| ^ (p + 1)
  rw [← hpoly, hrem, sub_zero, abs_div, abs_mul, abs_pow, abs_of_pos hfact]
  calc
    _ ≤ max M 1 * |h| ^ (p + 1) / ((p + 1).factorial : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hbound (pow_nonneg (abs_nonneg h) _)) hfact.le
    _ = Cp * |h| ^ (p + 1) := by dsimp only [Cp]; ring

#print axioms verticalIteratedDeriv_contDiffAt
#print axioms parametricTaylorCoefficient_contDiffAt
#print axioms parametricTaylor_uniform_remainder

end MF21Restart
