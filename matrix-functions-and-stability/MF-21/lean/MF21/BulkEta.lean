import MF21.BulkTotalPhase

noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace MF21Bulk

/-- One actual smooth extension of the phase eta to a fixed enlarged
closed interval. This supports a single uniform inverse and a common
coefficient family for all Taylor orders. -/
theorem eta_extension (m : ℕ) (hm : 0 < m) :
    ∃ eta : ℝ → ℝ, ∃ delta : ℝ, 0 < delta ∧
      (∀ theta ∈ Icc (-delta) (Real.pi + delta), ContDiffAt ℝ ∞ eta theta) ∧
      eta 0 = (m - 1 : ℝ) * Real.pi / 2 ∧ eta Real.pi = Real.pi ∧
      (∀ theta > 0, eta theta = theta + 2 * psi m theta) := by
  obtain ⟨P, d, hd, hP0, hPc, hPe⟩ := psi_endpoint_neighborhood m hm
  let Q : ℝ → ℝ := fun theta => if theta ≤ 0 then P theta else psi m theta
  let eta : ℝ → ℝ := fun theta => theta + 2 * Q theta
  let delta := min (d / 2) (Real.pi / 2)
  have hdelt : 0 < delta := lt_min (by positivity) (by positivity)
  have hdd : delta < d := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hdp : delta ≤ Real.pi / 2 := min_le_right _ _
  have hQP : Q =ᶠ[𝓝 0] P := by
    filter_upwards [Ioo_mem_nhds (by linarith : -d < (0 : ℝ)) hd] with theta ht
    by_cases ht0 : theta ≤ 0
    · exact if_pos ht0
    · exact (if_neg ht0).trans (hPe theta ⟨lt_of_not_ge ht0, ht.2⟩).symm
  have hQc (theta : ℝ) (ht : theta ∈ Icc (-delta) (Real.pi + delta)) :
      ContDiffAt ℝ ∞ Q theta := by
    rcases lt_trichotomy theta 0 with hn | hz | hp
    · have hc := hPc theta (show theta ∈ Ioo (-d) d by constructor <;> linarith [ht.1])
      apply hc.congr_of_eventuallyEq
      filter_upwards [gt_mem_nhds hn] with x hx
      exact if_pos hx.le
    · subst theta
      exact (hPc 0 ⟨by linarith, hd⟩).congr_of_eventuallyEq hQP
    · have htp : theta < 2 * Real.pi := by linarith [ht.2, Real.pi_pos]
      have hs : 0 < spectralBase theta := by
        apply sq_pos_of_pos
        exact mul_pos (by norm_num)
          (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
      apply (psi_contDiffAt m hm theta hs).congr_of_eventuallyEq
      filter_upwards [lt_mem_nhds hp] with x hx
      exact if_neg (not_le_of_gt hx)
  refine ⟨eta, delta, hdelt, ?_, ?_, ?_, ?_⟩
  · intro theta ht
    exact contDiffAt_id.add (contDiffAt_const.mul (hQc theta ht))
  · simp [eta, Q, hP0]
    ring
  · simp [eta, Q, not_le_of_gt Real.pi_pos, psi_pi m hm]
  · intro theta ht
    simp [eta, Q, not_le_of_gt ht]

end MF21Bulk

#print axioms MF21Bulk.eta_extension
