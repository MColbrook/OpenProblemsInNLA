import MF21Restart.ImplicitTaylor
import MF21Restart.SmoothCoefficient
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Separation.Hausdorff

/-! Independence of (5) from arbitrary smooth extensions. Interior
implicit germs agree by actual uniqueness; continuity extends equality
of all coefficients to both endpoints. Order infinity means C-infinity,
not analytic top. Prior lock: EXTENSION_INDEPENDENCE_STATEMENTS.md. -/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology ContDiff

namespace MF21Restart

/-- Every smooth competing implicit parametrization for extensions that
agree on the original interval has exactly the same coefficients there.
The extension of eta only needs agreement: its smoothness is not used
once a smooth competing implicit parametrization has been supplied. -/
theorem implicitPhaseCoefficient_extension_independent
    (m : ℕ) (Y : ℝ × ℝ → ℝ) (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε)
    (hY : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, ContDiffAt ℝ ∞ Y (x, 0))
    (huniq : ∀ p ∈ Set.Ioo (-r / 2) (Real.pi + r / 2) ×ˢ Set.Ioo (-ε) ε,
      ∀ y ∈ Set.Icc (-r) (Real.pi + r),
        y = p.1 + p.2 * manuscriptEta m y → y = Y p)
    (etaTilde gTilde : ℝ → ℝ) (Z : ℝ × ℝ → ℝ)
    (hEta : Set.EqOn etaTilde (manuscriptEta m) (Set.Icc 0 Real.pi))
    (hSymbol : Set.EqOn gTilde (symbol m) (Set.Icc 0 Real.pi))
    (hg : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, ContDiffAt ℝ ∞ gTilde x)
    (hZ : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, ContDiffAt ℝ ∞ Z (x, 0))
    (hZzero : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, Z (x, 0) = x)
    (hZeq : ∀ x ∈ Set.Ioo (0 : ℝ) Real.pi,
      ∀ᶠ h : ℝ in 𝓝 0, Z (x, h) = x + h * etaTilde (Z (x, h))) :
    ∀ k : ℕ, Set.EqOn
      (parametricTaylorCoefficient (fun p => gTilde (Z p)) k)
      (implicitPhaseCoefficient m Y k) (Set.Icc 0 Real.pi) := by
  intro k
  have hG : ContDiff ℝ ∞ (symbol m) := by
    unfold symbol
    fun_prop
  have hActual : ContinuousOn (implicitPhaseCoefficient m Y k) (Set.Icc 0 Real.pi) := by
    intro x hx
    have hF : ContDiffAt ℝ ∞ (fun p => symbol m (Y p)) (x, 0) :=
      hG.contDiffAt.comp (x, 0) (hY x hx)
    exact (parametricTaylorCoefficient_contDiffAt_infty _ k x hF).continuousAt.continuousWithinAt
  have hOther : ContinuousOn
      (parametricTaylorCoefficient (fun p => gTilde (Z p)) k) (Set.Icc 0 Real.pi) := by
    intro x hx
    have hgx : ContDiffAt ℝ ∞ gTilde (Z (x, 0)) := by
      rw [hZzero x hx]
      exact hg x hx
    have hF : ContDiffAt ℝ ∞ (fun p => gTilde (Z p)) (x, 0) :=
      hgx.comp (x, 0) (hZ x hx)
    exact (parametricTaylorCoefficient_contDiffAt_infty _ k x hF).continuousAt.continuousWithinAt
  have hinterior : Set.EqOn
      (parametricTaylorCoefficient (fun p => gTilde (Z p)) k)
      (implicitPhaseCoefficient m Y k) (Set.Ioo 0 Real.pi) := by
    intro x hx
    have hxc : x ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hx.1.le, hx.2.le⟩
    have hZcont : ContinuousAt (fun h : ℝ => Z (x, h)) 0 :=
      (hZ x hxc).continuousAt.comp (continuousAt_const.prodMk continuousAt_id)
    have hZlim : Tendsto (fun h : ℝ => Z (x, h)) (𝓝 0) (𝓝 x) := by
      simpa only [hZzero x hxc] using hZcont.tendsto
    have hinside : ∀ᶠ h : ℝ in 𝓝 0, Z (x, h) ∈ Set.Ioo (0 : ℝ) Real.pi :=
      hZlim (Ioo_mem_nhds hx.1 hx.2)
    have hstep : ∀ᶠ h : ℝ in 𝓝 0, h ∈ Set.Ioo (-ε) ε :=
      Ioo_mem_nhds (by linarith) hε
    have hgerm : (fun h : ℝ => gTilde (Z (x, h))) =ᶠ[𝓝 0]
        (fun h : ℝ => symbol m (Y (x, h))) := by
      filter_upwards [hinside, hstep, hZeq x hx] with h hz hh heq
      have hzc : Z (x, h) ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hz.1.le, hz.2.le⟩
      have hp : (x, h) ∈ Set.Ioo (-r / 2) (Real.pi + r / 2) ×ˢ Set.Ioo (-ε) ε := by
        refine ⟨⟨?_, ?_⟩, hh⟩ <;> linarith [hx.1, hx.2]
      have heqActual : Z (x, h) = x + h * manuscriptEta m (Z (x, h)) := by
        rw [← hEta hzc]
        exact heq
      have hZY : Z (x, h) = Y (x, h) :=
        huniq (x, h) hp (Z (x, h))
          (by constructor <;> linarith [hz.1, hz.2]) heqActual
      rw [hSymbol hzc, hZY]
    have hd := hgerm.iteratedDeriv_eq k
    change iteratedDeriv k (fun h : ℝ => gTilde (Z (x, h))) 0 / (k.factorial : ℝ) =
      iteratedDeriv k (fun h : ℝ => symbol m (Y (x, h))) 0 / (k.factorial : ℝ)
    rw [hd]
  apply hinterior.of_subset_closure hOther hActual
    (fun x hx => ⟨hx.1.le, hx.2.le⟩)
  rw [closure_Ioo (ne_of_lt Real.pi_pos)]

#print axioms implicitPhaseCoefficient_extension_independent

end MF21Restart
