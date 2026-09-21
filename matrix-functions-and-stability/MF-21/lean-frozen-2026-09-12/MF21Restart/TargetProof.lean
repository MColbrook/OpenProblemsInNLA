import MF21Restart.ImplicitExpansionBounds
import MF21Restart.ActualFixedIndex
import MF21Restart.SpectralTracePassage
import MF21Restart.ActualTraceLimit
import MF21Restart.TraceSeries
import MF21Restart.CirculantBounds

/-! Assembly of the unchanged MF21Restart.Target. One actual implicit
phase supplies every coefficient used in the global, bulk, and critical
arguments. Prior statement lock: TARGET_ASSEMBLY_STATEMENTS.md.
Local/compiler/Comparator status is recorded separately from this source. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology ContDiff

namespace MF21Restart

/-- The hypothetical critical uniform estimate forces two different
limits for the same actual scaled inverse trace. The actual circulant
bound supplies the Tannery majorant, including its exact index range. -/
theorem implicitPhase_critical_bound_impossible
    (m : ℕ) (hm : 3 ≤ m) (Y : ℝ × ℝ → ℝ)
    (r ε C δ : ℝ) (hr : 0 < r) (hε : 0 < ε) (hC : 0 < C) (hδ : 0 < δ)
    (hY : ∀ p ∈ Set.Ioo (-r / 2) (Real.pi + r / 2) ×ˢ Set.Ioo (-ε) ε,
      Y p ∈ Set.Ioo (-r) (Real.pi + r) ∧
        Y p = p.1 + p.2 * manuscriptEta m (Y p) ∧
        |Y p - p.1| ≤ C * |p.2|)
    (hTaylor : ∃ B : ℝ, 0 < B ∧
      ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, ∀ h : ℝ, |h| ≤ δ →
        |symbol m (Y (x, h)) -
            ∑ k ∈ Finset.range (2 * m + 1), implicitPhaseCoefficient m Y k x * h ^ k| ≤
          B * |h| ^ (2 * m + 1)) :
    ¬UniformBound m (implicitPhaseCoefficient m Y) (2 * m) := by
  intro hU
  have hm1 : 1 ≤ m := by omega
  have hfixed := critical_bound_implies_actual_fixed_index_limit m hm1 Y r ε C δ
    hr hε hC hδ hY hTaylor hU
  have hseries := toeplitz_inverse_trace_tendsto_series_of_limits_and_majorant m hm1
    hfixed (eigenvalue_eventual_reciprocal_tail_bound m hm1)
  have hkernel := toeplitz_inverse_trace_tendsto_mesh m hm1
  have heq := tendsto_nhds_unique hseries hkernel
  obtain ⟨q, hq⟩ := kernelTraceConstant_rational m
  exact (trace_series_irrational m hm) ⟨q, (heq.trans hq).symm⟩

/-- The manuscript's smooth coefficient family satisfies all three
original conclusions. Smooth order infinity is distinct from analytic top. -/
theorem manuscript_smooth_target :
    ∀ m : ℕ, 3 ≤ m → ∃ d : ℕ → ℝ → ℝ,
      (∀ k ≤ 2 * m, ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, ContDiffAt ℝ ∞ (d k) x) ∧
      Set.EqOn (d 0) (symbol m) (Set.Icc 0 Real.pi) ∧
      (∀ p ≤ 2 * m - 1, UniformBound m d p) ∧
      BulkBound m d ∧ ¬UniformBound m d (2 * m) := by
  intro m hm
  have hm1 : 1 ≤ m := by omega
  obtain ⟨r, ε, C, δ, hr, hε, hC, hδ, _hδε, Y,
    _hYreg, hYeq, _hYzero, _hYuniq, hcoeff, hzero, hTaylor, hvan,
    N, J, Cs, c, _hN, _hJ, hCs, hc, htail⟩ :=
    manuscript_implicit_taylor_with_spectral_error m (by omega)
  have hTail : ∀ n : ℕ, N ≤ n → ∀ j : ℕ, J ≤ j → j ≤ n →
      |eigenvalue m n j - symbol m (Y (mesh n j, 1 / (n + 2 : ℝ)))| ≤
        Cs * (1 / (n + 2 : ℝ)) ^ (2 * m) * (j : ℝ) ^ (2 * m - 1) *
          Real.exp (-c * (j : ℝ)) := by
    intro n hn j hj hjn
    obtain ⟨θ, _hθ, _hy, _hev, _hdist, _hθsize, _hysize, he⟩ := htail n hn j hj hjn
    exact he
  have hbounds := implicitPhase_expansion_bounds_of_data m hm1 Y δ hδ
    hTaylor hvan N J Cs c hCs hc hTail
  have hglobal := hbounds.2 (eigenvalue_fixed_prefix_bound m hm1)
  have hnot := implicitPhase_critical_bound_impossible m hm Y r ε C δ
    hr hε hC hδ hYeq (hTaylor (2 * m))
  refine ⟨implicitPhaseCoefficient m Y, ?_, ?_, hglobal, hbounds.1, hnot⟩
  · intro k _hk x hx
    apply (hcoeff k x ?_).of_le le_top
    constructor <;> linarith [hx.1, hx.2]
  · intro x hx
    apply hzero x
    constructor <;> linarith [hx.1, hx.2]

/-- The unchanged canonical Target follows for exactly the same smooth
coefficient family, without an additional existential construction. -/
theorem target_proved : Target := by
  intro m hm
  obtain ⟨d, hsmooth, hzero, hglobal, hbulk, hnot⟩ := manuscript_smooth_target m hm
  refine ⟨d, ?_, hzero, hglobal, hbulk, hnot⟩
  intro k hk x hx
  exact (hsmooth k hk x hx).continuousAt.continuousWithinAt

#print axioms implicitPhase_critical_bound_impossible
#print axioms manuscript_smooth_target
#print axioms target_proved

end MF21Restart
