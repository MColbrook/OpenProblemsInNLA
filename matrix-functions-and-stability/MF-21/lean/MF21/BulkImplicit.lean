import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

/-! Local smooth construction of the scalar implicit equation
Y(x,h) = x + h eta(Y(x,h)). The phase eta is an input function;
the existence and smoothness of the solution are proved here. -/

open Filter
open scoped Topology ContDiff
noncomputable section
namespace MF21Bulk

theorem local_implicit_solution (eta : ℝ → ℝ) (heta : ContDiff ℝ ∞ eta) (x : ℝ) :
    ∃ Y : ℝ × ℝ → ℝ,
      Y (x, 0) = x ∧
      ContDiffAt ℝ ∞ Y (x, 0) ∧
      (∀ᶠ p : ℝ × ℝ in 𝓝 (x, 0), Y p = p.1 + p.2 * eta (Y p)) ∧
      (∀ᶠ p : (ℝ × ℝ) × ℝ in 𝓝 ((x, 0), x),
        p.2 = p.1.1 + p.1.2 * eta p.2 ↔ Y p.1 = p.2) := by
  let F : (ℝ × ℝ) × ℝ → ℝ := fun p => p.2 - p.1.1 - p.1.2 * eta p.2
  have hc : ContDiffAt ℝ ∞ F ((x, 0), x) := by
    dsimp [F]
    fun_prop
  have hd : fderiv ℝ F ((x, 0), x) ∘L
      ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ = ContinuousLinearMap.id ℝ ℝ := by
    have hcomp := (hc.differentiableAt (by simp)).hasFDerivAt.comp x
      ((hasFDerivAt_const (x, (0 : ℝ)) x).prodMk (hasFDerivAt_id x))
    have hsimple : HasFDerivAt (fun y : ℝ => y - x)
        (fderiv ℝ F ((x, 0), x) ∘L ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ) x := by
      simpa [F, Function.comp_def, ContinuousLinearMap.inr] using hcomp
    exact hsimple.unique ((hasFDerivAt_id x).sub_const x)
  have hinv : (fderiv ℝ F ((x, 0), x) ∘L
      ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ).IsInvertible := by
    rw [hd]
    exact ⟨ContinuousLinearEquiv.refl ℝ ℝ, rfl⟩
  let Y := hc.implicitFunction (by simp) hinv
  refine ⟨Y, hc.implicitFunction_apply_self (by simp) hinv,
    hc.contDiffAt_implicitFunction (by simp) hinv, ?_, ?_⟩
  · filter_upwards [hc.eventually_apply_implicitFunction (by simp) hinv] with p hp
    dsimp [F] at hp
    simp only [sub_self, zero_mul] at hp
    change Y p - p.1 - p.2 * eta (Y p) = 0 at hp
    linarith
  · filter_upwards [hc.eventually_apply_eq_iff_implicitFunction (by simp) hinv] with p hp
    dsimp [F] at hp
    simp only [sub_self, zero_mul] at hp
    change (p.2 - p.1.1 - p.1.2 * eta p.2 = 0 ↔ Y p.1 = p.2) at hp
    convert hp using 1
    constructor <;> intro h <;> linarith

theorem implicit_contraction (eta : ℝ → ℝ) {K : NNReal}
    (heta : LipschitzWith K eta) (x h : ℝ) (hh : |h| * K < 1) :
    ContractingWith (‖h‖₊ * K) (fun y : ℝ => x + h * eta y) := by
  constructor
  · exact_mod_cast hh
  · apply LipschitzWith.of_dist_le_mul
    intro y z
    have hb := mul_le_mul_of_nonneg_left (heta.dist_le_mul y z) (abs_nonneg h)
    simpa [Real.dist_eq, ← mul_sub, abs_mul, mul_assoc] using hb

/-- A global Lipschitz phase has one implicit solution at every base point,
with a matrix-size parameter bound independent of that base point. -/
theorem existsUnique_implicit_solution (eta : ℝ → ℝ) {K : NNReal}
    (heta : LipschitzWith K eta) (x h : ℝ) (hh : |h| * K < 1) :
    ∃! y : ℝ, y = x + h * eta y := by
  let hc := implicit_contraction eta heta x h hh
  refine ⟨hc.fixedPoint (fun y : ℝ => x + h * eta y), ?_, ?_⟩
  · exact hc.fixedPoint_isFixedPt.symm
  · intro y hy
    exact hc.fixedPoint_unique hy.symm

end MF21Bulk

#print axioms MF21Bulk.local_implicit_solution
#print axioms MF21Bulk.implicit_contraction
#print axioms MF21Bulk.existsUnique_implicit_solution
