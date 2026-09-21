import MF21Restart.ParametricTaylor

/-! Smooth (order infinity, not analytic top) regularity of exact
vertical derivatives, for arbitrary smooth extension comparisons.
Prior lock: EXTENSION_INDEPENDENCE_STATEMENTS.md. -/

set_option autoImplicit false
noncomputable section
open scoped ContDiff

namespace MF21Restart

set_option backward.isDefEq.respectTransparency.types false in
theorem verticalIteratedDeriv_contDiffAt_infty
    (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (hF : ContDiffAt ℝ ∞ F p) (k : ℕ) :
    ContDiffAt ℝ ∞ (verticalIteratedDeriv F k) p := by
  induction k with
  | zero =>
    have hzero : verticalIteratedDeriv F 0 = F := by
      funext q
      simp only [verticalIteratedDeriv, iteratedDeriv_zero]
    rw [hzero]
    exact hF
  | succ k ih =>
    have hjoint : ContDiffAt ℝ ∞
        (Function.uncurry (fun q : ℝ × ℝ => fun t : ℝ =>
          verticalIteratedDeriv F k (q.1, t))) (p, p.2) :=
      ih.comp (p, p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hd : ContDiffAt ℝ ∞
        (fun q : ℝ × ℝ =>
          fderiv ℝ (fun t : ℝ => verticalIteratedDeriv F k (q.1, t)) q.2) p :=
      hjoint.fderiv contDiffAt_snd (by simp)
    have he := hd.clm_apply
      (show ContDiffAt ℝ ∞ (fun _ : ℝ × ℝ => (1 : ℝ)) p from contDiffAt_const)
    have hstep : verticalIteratedDeriv F (k + 1) =
        fun q : ℝ × ℝ =>
          (fderiv ℝ (fun t : ℝ => verticalIteratedDeriv F k (q.1, t)) q.2) 1 := by
      funext q
      change iteratedDeriv (k + 1) (fun h : ℝ => F (q.1, h)) q.2 =
        deriv (iteratedDeriv k (fun h : ℝ => F (q.1, h))) q.2
      rw [iteratedDeriv_succ]
    rw [hstep]
    exact he

theorem parametricTaylorCoefficient_contDiffAt_infty
    (F : ℝ × ℝ → ℝ) (k : ℕ) (x : ℝ)
    (hF : ContDiffAt ℝ ∞ F (x, 0)) :
    ContDiffAt ℝ ∞ (parametricTaylorCoefficient F k) x := by
  have hd := verticalIteratedDeriv_contDiffAt_infty F (x, 0) hF k
  have hc := hd.comp x (contDiffAt_id.prodMk contDiffAt_const)
  exact hc.div_const (k.factorial : ℝ)

#print axioms verticalIteratedDeriv_contDiffAt_infty
#print axioms parametricTaylorCoefficient_contDiffAt_infty

end MF21Restart
