import MF21.PhaseCutoffs
import MF21.ActualBoundarySimplicity
import MF21.ActualBoundaryPhase
import MF21.ActualBoundarySmooth
import MF21.QuantizationTaylor

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace MF21ActualBoundary
open MF21Challenge MF21Quantization MF21Phase

/-- Compactness bounds the actual smooth phase and its derivative. -/
theorem model_phase_bounds (m : ℕ) (model : Model m) :
    ∃ M K : ℝ, 0 ≤ M ∧
      (∀ t ∈ Icc 0 Real.pi, |model.eta t| ≤ M) ∧
      (∀ t ∈ Icc 0 Real.pi, |deriv model.eta t| ≤ K) := by
  have he : ContinuousOn model.eta (Icc 0 Real.pi) :=
    fun t ht ↦ (model.eta_smooth t ht).continuousAt.continuousWithinAt
  have hd : ContinuousOn (deriv model.eta) (Icc 0 Real.pi) :=
    fun t ht ↦ ((model.eta_smooth t ht).derivWithin (m := 0) (by simp)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image he.abs
  obtain ⟨K, hK⟩ := isCompact_Icc.bddAbove_image hd.abs
  refine ⟨max M 0, K, le_max_right _ _, ?_, ?_⟩
  · intro t ht
    exact (hM (mem_image_of_mem _ ht)).trans (le_max_left _ _)
  · intro t ht
    exact hK (mem_image_of_mem _ ht)

theorem phase_eq_quantizationPhase (eta : ℝ → ℝ) (n : ℕ) (t : ℝ) :
    phase n eta t = quantizationPhase eta n t := by
  simp [phase, quantizationPhase]

/-- The actual determinant zeros and the actual eigenangles coincide. -/
theorem sine_zero_iff_eigenangle (m n : ℕ) (hm : 0 < m) (d : SlopeData m)
    (model : Model m) (t : ℝ) (ht : t ∈ Ioo 0 Real.pi) :
    Real.sin (phase n model.eta t)+realError m hm d model.eta n t = 0 ↔
      ∃ i : Fin n, eigenangle m n hm i = t := by
  rw [phase_eq_quantizationPhase, ← determinant_zero_iff_sine m n hm d model.eta t ⟨ht.1,le_of_lt ht.2⟩
    (model.eta_actual t ht.1), ← sorted_eigenvalue_iff_determinant_zero m n hm t ht.1 ht.2]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (eigenangle_eq_iff m n hm i t ht).mpr hi.symm⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, ((eigenangle_eq_iff m n hm i t ht).mp hi).symm⟩

theorem actual_phase_error_bounds (m : ℕ) (hm : 0 < m) (d : SlopeData m)
    (model : Model m) : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (∀ t ∈ Ioo 0 Real.pi,
        |realError m hm d model.eta n t| ≤ C*Real.exp (-c*n*t) ∧
        |deriv (realError m hm d model.eta n) t| ≤ C*n*Real.exp (-c*n*t)) ∧
      (∀ t ∈ Ioo 0 Real.pi, Real.pi/2 ≤ t →
        |realError m hm d model.eta n t| ≤
          C*n*Real.exp (-(c*Real.pi/2)*n)*(Real.pi-t)) := by
  obtain ⟨c, hc, C, hC, hb⟩ := realError_bounds m hm d model.eta model.eta_smooth
  refine ⟨c, 2*C, hc, by positivity, ?_⟩
  intro n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · intro t ht
    obtain ⟨hv, hd⟩ := hb n t ⟨ht.1,le_of_lt ht.2⟩
    constructor
    · apply hv.trans
      have hE : 0 < Real.exp (-c*n*t) := Real.exp_pos _
      nlinarith
    · apply hd.trans
      have hE : 0 < Real.exp (-c*n*t) := Real.exp_pos _
      have hmul := mul_le_mul_of_nonneg_right (show C*((n : ℝ)+1) ≤ 2*C*n by nlinarith)
        (le_of_lt hE)
      exact hmul
  · intro t ht htp
    have hdiff (x : ℝ) (hx : x ∈ Icc (Real.pi/2) Real.pi) :
        DifferentiableAt ℝ (realError m hm d model.eta n) x := by
      have hx' : x ∈ Icc 0 Real.pi := ⟨(by linarith [Real.pi_pos,hx.1]),hx.2⟩
      exact (realError_smooth m hm d model.eta n x hx' (model.eta_smooth x hx')).differentiableAt (by simp)
    have hderbd (x : ℝ) (hx : x ∈ Icc (Real.pi/2) Real.pi) :
        |deriv (realError m hm d model.eta n) x| ≤ C*(n+1)*Real.exp (-c*n*x) :=
      (hb n x ⟨(by linarith [Real.pi_pos,hx.1]),hx.2⟩).2
    have hh := endpoint_sensitive_error_bound (realError m hm d model.eta n) n c C
      hc (le_of_lt hC) hdiff hderbd (realError_pi m n hm d model.eta model.eta_pi)
      t ⟨htp,le_of_lt ht.2⟩
    apply hh.trans
    have heq : -c*n*Real.pi/2 = -(c*Real.pi/2)*n := by ring
    rw [heq]
    have hfactor : 0 ≤ (Real.pi-t)*Real.exp (-(c*Real.pi/2)*n) := by
      exact mul_nonneg (by linarith [ht.2]) (le_of_lt (Real.exp_pos _))
    nlinarith [mul_le_mul_of_nonneg_right
      (show C*((n : ℝ)+1) ≤ 2*C*n by nlinarith) hfactor]

/-- The actual normalized determinant has simple indexed eigenangle zeros
whenever its real secular derivative is nonzero. -/
theorem simple_sine_zero_unique_index (m n : ℕ) (hm : 0 < m) (d : SlopeData m)
    (model : Model m) (t : ℝ) (ht : t ∈ Ioo 0 Real.pi)
    (hz : Real.sin (phase n model.eta t)+realError m hm d model.eta n t = 0)
    (hd : deriv (fun x ↦ Real.sin (phase n model.eta x)+realError m hm d model.eta n x) t ≠ 0)
    (i k : Fin n) (hi : eigenangle m n hm i = t) (hk : eigenangle m n hm k = t) : i = k := by
  have htc : t ∈ Icc 0 Real.pi := ⟨le_of_lt ht.1,le_of_lt ht.2⟩
  have hF : DifferentiableAt ℝ
      (fun x ↦ Real.sin (phase n model.eta x)+realError m hm d model.eta n x) t := by
    apply DifferentiableAt.add
    · apply DifferentiableAt.sin
      unfold phase
      exact ((differentiableAt_const ((n : ℝ)+2)).mul differentiableAt_id).sub
        ((model.eta_smooth t htc).differentiableAt (by simp))
    · exact (realError_smooth m hm d model.eta n t htc (model.eta_smooth t htc)).differentiableAt (by simp)
  have heq : (fun x ↦ determinant m n x) =ᶠ[𝓝 t]
      (fun x ↦ sineNormalizer m n x *
        ((Real.sin (phase n model.eta x)+realError m hm d model.eta n x : ℝ) : ℂ)) := by
    filter_upwards [isOpen_Ioo.eventually_mem ht] with x hx
    rw [phase_eq_quantizationPhase]
    exact determinant_realError m n hm d model.eta x ⟨hx.1,le_of_lt hx.2⟩ (model.eta_actual x hx.1)
  exact unique_eigenangle_index_of_simple_normalized_zero m n hm _ (sineNormalizer m n)
    t ht hF ((sineNormalizer_contDiffAt m n hm t ht).differentiableAt (by simp)) heq
    (sineNormalizer_nonzero m n hm d t ⟨ht.1,le_of_lt ht.2⟩) hz hd i k hi hk

/-- The actual eigenangle with source index j lies in its own phase cell
and has an exponentially small phase residual, uniformly above a fixed index. -/
theorem actual_indexed_phase_roots (m : ℕ) (hm : 0 < m) (model : Model m) :
    ∃ J N : ℕ, ∃ M C c : ℝ,
      1 ≤ J ∧ 1 ≤ N ∧ 0 ≤ M ∧ 0 < C ∧ 0 < c ∧
      (∀ t ∈ Icc 0 Real.pi, |model.eta t| ≤ M) ∧
      ∀ n, N ≤ n → ∀ j : Fin n, J ≤ j.val+1 →
      |phase n model.eta (eigenangle m n hm j)-(j.val+1)*Real.pi| ≤ Real.pi/4 ∧
      |phase n model.eta (eigenangle m n hm j)-(j.val+1)*Real.pi| ≤
        C*Real.exp (-c*n*(eigenangle m n hm j)) := by
  let d : SlopeData m := Classical.choice (slopeData_exists m hm)
  obtain ⟨M, K, hM, heta, hdeta⟩ := model_phase_bounds m model
  obtain ⟨c, C, hc, hC, hbd⟩ := actual_phase_error_bounds m hm d model
  have hder (t : ℝ) (ht : t ∈ Icc 0 Real.pi) : HasDerivAt model.eta (deriv model.eta t) t :=
    ((model.eta_smooth t ht).differentiableAt (by simp)).hasDerivAt
  have hEder (n : ℕ) (_hn : 1 ≤ n) (t : ℝ) (ht : t ∈ Ioo 0 Real.pi) :
      HasDerivAt (realError m hm d model.eta n) (deriv (realError m hm d model.eta n) t) t := by
    have htc : t ∈ Icc 0 Real.pi := ⟨le_of_lt ht.1,le_of_lt ht.2⟩
    exact ((realError_smooth m hm d model.eta n t htc (model.eta_smooth t htc)).differentiableAt (by simp)).hasDerivAt
  obtain ⟨J,N,hJ,hN,_,hroots⟩ := eventual_indexed_phase_roots model.eta (deriv model.eta)
    (realError m hm d model.eta) (fun n ↦ deriv (realError m hm d model.eta n))
    M K C c hM (le_of_lt hC) hc heta hder hdeta model.eta_pi 1
    (fun n ↦ eigenangle m n hm) (fun n ↦ eigenangle_monotone m n hm)
    (fun n j ↦ eigenangle_mem m n hm j) hEder
    (fun n hn ↦ (hbd n hn).1) (fun n hn ↦ (hbd n hn).2)
    (fun n _ t ht ↦ sine_zero_iff_eigenangle m n hm d model t ht)
    (fun n _ t ht hz hd i k hi hk ↦ simple_sine_zero_unique_index m n hm d model t ht hz hd i k hi hk)
  refine ⟨J,N,M,(Real.pi/2)*C,c,hJ,hN,hM,by positivity,hc,heta,?_⟩
  intro n hn j hj
  have hh := hroots n hn j hj
  refine ⟨hh.1, ?_⟩
  have hb := ((hbd n (hN.trans hn)).1 (eigenangle m n hm j) (eigenangle_mem m n hm j)).1
  exact hh.2.2.trans (by nlinarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ Real.pi/2 by positivity)])

end MF21ActualBoundary

#print axioms MF21ActualBoundary.model_phase_bounds
#print axioms MF21ActualBoundary.sine_zero_iff_eigenangle
#print axioms MF21ActualBoundary.actual_phase_error_bounds

#print axioms MF21ActualBoundary.simple_sine_zero_unique_index
#print axioms MF21ActualBoundary.actual_indexed_phase_roots
