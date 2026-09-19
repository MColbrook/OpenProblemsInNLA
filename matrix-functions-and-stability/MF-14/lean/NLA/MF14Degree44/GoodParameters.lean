import NLA.MF14Degree44.Definitions
import Mathlib.Topology.Separation.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import LeanCert.Tactic.Verification

/-!
Good parameters for Marcus Webb's border construction, The University of
Manchester. Formalization: George Stepaniants, Department of Computing and
Mathematical Sciences, California Institute of Technology; Codex assistance.
The special gamma=0 case is included explicitly. No numerical approximation.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped Topology
namespace NLA.MF14Degree44

theorem good_border_parameters_eventually (alpha eta gamma : ℂ) :
    ∀ᶠ s in nhdsWithin (0 : ℂ) ({0}ᶜ), GoodBorderParameter alpha eta gamma s := by
  have hs : ∀ᶠ s in nhdsWithin (0 : ℂ) ({0}ᶜ), s ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      (eventually_mem_nhdsWithin : ∀ᶠ s in nhdsWithin (0 : ℂ) ({0}ᶜ), s ∈ ({0}ᶜ : Set ℂ))
  have hdelta : ∀ᶠ s in nhdsWithin (0 : ℂ) ({0}ᶜ), gamma * s - 2 * s ^ 2 ≠ 0 := by
    by_cases hg : gamma = 0
    · filter_upwards [hs] with s hs
      have hfactor : gamma * s - 2 * s ^ 2 = (-2 : ℂ) * s ^ 2 := by rw [hg]; ring
      rw [hfactor]
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hs)
    · have hc : ContinuousAt (fun s : ℂ => gamma - 2 * s) 0 := by fun_prop
      have hn : ∀ᶠ s in nhdsWithin (0 : ℂ) ({0}ᶜ), gamma - 2 * s ≠ 0 :=
        (hc.eventually_ne (by simpa using hg)).filter_mono nhdsWithin_le_nhds
      filter_upwards [hs, hn] with s hs hn
      have hfactor : gamma * s - 2 * s ^ 2 = s * (gamma - 2 * s) := by ring
      rw [hfactor]
      exact mul_ne_zero hs hn
  let bracket : ℂ → ℂ := fun s =>
    eta + 1 - eta - alpha * (eta + 1) * (gamma * s - s ^ 2 * (eta + 1))
  have hb : ContinuousAt bracket 0 := by dsimp [bracket]; fun_prop
  have hb0 : bracket 0 ≠ 0 := by simp [bracket]
  have hbracket : ∀ᶠ s in nhdsWithin (0 : ℂ) ({0}ᶜ), bracket s ≠ 0 :=
    (hb.eventually_ne hb0).filter_mono nhdsWithin_le_nhds
  filter_upwards [hs, hdelta, hbracket] with s hs hd hb
  refine ⟨hs, hd, ?_⟩
  change (s ^ 2) ^ 5 * bracket s ≠ 0
  exact mul_ne_zero (pow_ne_zero 5 (pow_ne_zero 2 hs)) hb

#print axioms good_border_parameters_eventually
#assert_trust kernel good_border_parameters_eventually

end NLA.MF14Degree44
