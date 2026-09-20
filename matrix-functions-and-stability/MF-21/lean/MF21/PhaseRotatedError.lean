import MF21.ActualBoundaryError
import MF21.BulkPhase

/-! Rotation of the complex boundary remainder into the sine normalization. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Topology ContDiff
open Set
namespace MF21ActualBoundary
open MF21Bulk

def phaseRotate (F : ℝ → ℝ) (R : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Complex.I/2)*unitRoot (-F x)*R x

theorem phaseRotate_norm (F : ℝ → ℝ) (R : ℝ → ℂ) (x : ℝ) :
    ‖phaseRotate F R x‖ = ‖R x‖/2 := by
  simp [phaseRotate, norm_mul, norm_div, unitRoot_norm, div_eq_mul_inv, mul_comm]

theorem unitRoot_comp_hasDerivAt (F : ℝ → ℝ) (x f' : ℝ) (hf : HasDerivAt F f' x) :
    HasDerivAt (fun t => unitRoot (-F t))
      (unitRoot (-F x)*(-(f' : ℂ)*Complex.I)) x := by
  have hc := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x hf
  have h := (hc.neg.mul_const Complex.I).cexp
  simpa [unitRoot] using h

theorem phaseRotate_deriv_norm (F : ℝ → ℝ) (R : ℝ → ℂ) (x f' : ℝ) (r' : ℂ)
    (hf : HasDerivAt F f' x) (hr : HasDerivAt R r' x) :
    ‖deriv (phaseRotate F R) x‖ ≤ (‖r'‖+|f'| *‖R x‖)/2 := by
  have hu := unitRoot_comp_hasDerivAt F x f' hf
  have he := ((hu.const_mul (Complex.I/2)).fun_mul hr).deriv
  unfold phaseRotate
  rw [he]
  calc
    _ ≤ ‖(Complex.I/2)*(unitRoot (-F x)*(-(f' : ℂ)*Complex.I))*R x‖ +
        ‖((Complex.I/2)*unitRoot (-F x))*r'‖ := norm_add_le _ _
    _ = _ := by simp [norm_mul, norm_div, unitRoot_norm]; ring

def quantizationPhase (eta : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (n+2)*x-eta x

def complexError (m : ℕ) (hm : 0<m) (d : SlopeData m) (eta : ℝ → ℝ)
    (n : ℕ) : ℝ → ℂ :=
  phaseRotate (quantizationPhase eta n) (normalizedRemainder m hm d (n+m))

theorem normalizedRemainder_smooth (m : ℕ) (hm : 0<m) (d : SlopeData m)
    (p : ℕ) (x : ℝ) (hx : x ∈ Icc 0 Real.pi) :
    ContDiffAt ℝ ∞ (normalizedRemainder m hm d p) x := by
  classical
  apply ContDiffAt.sum
  intro σ _
  exact (d.coefficient_smooth σ.val x hx).mul ((d.base_smooth hm σ.val x hx).pow p)

theorem quantizationPhase_hasDerivAt (eta : ℝ → ℝ) (n : ℕ) (x : ℝ)
    (he : DifferentiableAt ℝ eta x) :
    HasDerivAt (quantizationPhase eta n) ((n+2)-deriv eta x) x := by
  convert! ((hasDerivAt_id x).const_mul ((n : ℝ)+2)).fun_sub he.hasDerivAt using 1 <;>
    simp [quantizationPhase]

/-- The n-dependent phase rotation preserves exponential smallness and adds
only one linear factor in n to the derivative bound. -/
theorem complexError_bounds (m : ℕ) (hm : 0<m) (d : SlopeData m)
    (eta : ℝ → ℝ) (he : ∀ x ∈ Icc 0 Real.pi, ContDiffAt ℝ ∞ eta x) :
    ∃ c : ℝ, 0<c ∧ ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, ∀ x ∈ Ioc 0 Real.pi,
      ‖complexError m hm d eta n x‖ ≤ C*Real.exp (-c*n*x) ∧
      ‖deriv (complexError m hm d eta n) x‖ ≤ C*(n+1)*Real.exp (-c*n*x) := by
  obtain ⟨c,hc,A,hA,hbound⟩ := normalizedRemainder_bounds m hm d
  have hcde : ContinuousOn (deriv eta) (Icc 0 Real.pi) := by
    intro x hx
    have h : ContDiffAt ℝ 0 (deriv eta) x := (he x hx).derivWithin (by simp)
    exact h.continuousAt.continuousWithinAt
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcde
  let K := max M 0
  have hK : 0≤K := le_max_right _ _
  have hder : ∀ x ∈ Icc 0 Real.pi, |deriv eta x| ≤ K :=
    fun x hx => (hM x hx).trans (le_max_left _ _)
  let C := A*(m+K+4)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨c,hc,C,hC,?_⟩
  intro n x hx
  have hx' : x ∈ Icc 0 Real.pi := ⟨hx.1.le,hx.2⟩
  obtain ⟨hR,hRd⟩ := hbound (n+m) x hx
  have hp : Real.exp (-c*(n+m)*x) ≤ Real.exp (-c*n*x) := by
    apply Real.exp_le_exp.mpr
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    nlinarith [mul_nonneg (mul_nonneg hc.le hm0) hx.1.le]
  have hR' : ‖normalizedRemainder m hm d (n+m) x‖ ≤ A*Real.exp (-c*n*x) := by
    apply hR.trans
    simp only [Nat.cast_add]
    exact mul_le_mul_of_nonneg_left hp hA.le
  have hRd' : ‖deriv (normalizedRemainder m hm d (n+m)) x‖ ≤
      A*((n : ℝ)+m+1)*Real.exp (-c*n*x) := by
    apply hRd.trans
    simp only [Nat.cast_add]
    exact mul_le_mul_of_nonneg_left hp (by positivity)
  have hF := quantizationPhase_hasDerivAt eta n x ((he x hx').differentiableAt (by simp))
  have hFbound : |(n+2 : ℝ)-deriv eta x| ≤ n+2+K := by
    calc
      _ ≤ |(n+2 : ℝ)|+|deriv eta x| := abs_sub _ _
      _ ≤ _ := by rw [abs_of_nonneg (by positivity)]; linarith [hder x hx']
  constructor
  · rw [complexError, phaseRotate_norm]
    have hAC : A≤C := by
      dsimp [C]
      calc
        A = A*1 := (mul_one A).symm
        _ ≤ A*(m+K+4) := mul_le_mul_of_nonneg_left (by have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith) hA.le
    calc
      _ ≤ (A*Real.exp (-c*n*x))/2 := div_le_div_of_nonneg_right hR' (by norm_num)
      _ ≤ A*Real.exp (-c*n*x) := by nlinarith [show 0≤A*Real.exp (-c*n*x) by positivity]
      _ ≤ C*Real.exp (-c*n*x) := mul_le_mul_of_nonneg_right hAC (Real.exp_pos _).le
  · have hr := ((normalizedRemainder_smooth m hm d (n+m) x hx').differentiableAt (by simp)).hasDerivAt
    have hh := phaseRotate_deriv_norm (quantizationPhase eta n)
      (normalizedRemainder m hm d (n+m)) x _ _ hF hr
    change ‖deriv (complexError m hm d eta n) x‖ ≤ _ at hh
    apply hh.trans
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hprod : |(n+2 : ℝ)-deriv eta x| * ‖normalizedRemainder m hm d (n+m) x‖ ≤
        (n+2+K)*(A*Real.exp (-c*n*x)) :=
      mul_le_mul hFbound hR' (norm_nonneg _) (by positivity)
    have hcoef : (((n : ℝ)+m+1)+(n+2+K))/2 ≤ (m+K+4)*(n+1) := by
      nlinarith [mul_nonneg hm0 hn0, mul_nonneg hK hn0]
    calc
      _ ≤ (A*((n : ℝ)+m+1)*Real.exp (-c*n*x) +
          (n+2+K)*(A*Real.exp (-c*n*x)))/2 := by gcongr
      _ = A*((((n : ℝ)+m+1)+(n+2+K))/2)*Real.exp (-c*n*x) := by ring
      _ ≤ A*((m+K+4)*(n+1))*Real.exp (-c*n*x) := by gcongr
      _ = _ := by dsimp [C]; ring


end MF21ActualBoundary
#print axioms MF21ActualBoundary.complexError_bounds
