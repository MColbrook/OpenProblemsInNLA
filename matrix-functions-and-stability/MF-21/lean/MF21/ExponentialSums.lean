import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-! Uniform value and derivative estimates for a finite exponential sum. -/
noncomputable section
open scoped BigOperators Topology ContDiff
open Finset Set
namespace MF21ExpSums

theorem hasDerivAt_coefficient_power (a b : ℝ → ℂ) (x : ℝ) (a' b' : ℂ)
    (ha : HasDerivAt a a' x) (hb : HasDerivAt b b' x) (hb0 : b x ≠ 0) (p : ℕ) :
    HasDerivAt (fun t => a t * b t^p)
      ((a' + a x*(p : ℂ)*(b'/b x))*b x^p) x := by
  convert ha.fun_mul (hb.fun_pow p) using 1 <;> try rfl
  cases p with
  | zero => simp
  | succ p =>
    simp only [Nat.succ_sub_one, pow_succ]
    field_simp

theorem coefficient_power_norm_bounds (a b : ℝ → ℂ) (x : ℝ) (a' b' : ℂ)
    (ha : HasDerivAt a a' x) (hb : HasDerivAt b b' x) (hb0 : b x ≠ 0)
    (A D L ρ : ℝ) (hA : ‖a x‖ ≤ A) (hD : ‖a'‖ ≤ D)
    (hL : ‖b'/b x‖ ≤ L) (hρ : ‖b x‖ ≤ ρ) (p : ℕ) :
    ‖a x * b x^p‖ ≤ A*ρ^p ∧
      ‖deriv (fun t => a t*b t^p) x‖ ≤ (D+A*p*L)*ρ^p := by
  have hA0 := (norm_nonneg (a x)).trans hA
  have hD0 := (norm_nonneg a').trans hD
  have hL0 := (norm_nonneg (b'/b x)).trans hL
  have hρ0 := (norm_nonneg (b x)).trans hρ
  constructor
  · rw [norm_mul, norm_pow]
    gcongr
  · rw [(hasDerivAt_coefficient_power a b x a' b' ha hb hb0 p).deriv,
      norm_mul, norm_pow]
    have hcoeff : ‖a' + a x*(p : ℂ)*(b'/b x)‖ ≤ D+A*p*L := by
      calc
        _ ≤ ‖a'‖ + ‖a x*(p : ℂ)*(b'/b x)‖ := norm_add_le _ _
        _ = ‖a'‖ + ‖a x‖*(p : ℝ)*‖b'/b x‖ := by simp [norm_mul]
        _ ≤ D+A*p*L := by gcongr
    exact mul_le_mul hcoeff (pow_le_pow_left₀ (norm_nonneg _) hρ p)
      (pow_nonneg (norm_nonneg _) p) (by positivity)

/-- A finite geometric sum has the advertised uniform first-derivative loss. -/
theorem finite_sum_norm_bounds {ι : Type*} [Fintype ι]
    (a b : ι → ℝ → ℂ) (x : ℝ) (a' b' : ι → ℂ)
    (ha : ∀ i, HasDerivAt (a i) (a' i) x)
    (hb : ∀ i, HasDerivAt (b i) (b' i) x) (hb0 : ∀ i, b i x ≠ 0)
    (A D L ρ : ℝ) (hA : ∀ i, ‖a i x‖ ≤ A) (hD : ∀ i, ‖a' i‖ ≤ D)
    (hL : ∀ i, ‖b' i/b i x‖ ≤ L) (hρ : ∀ i, ‖b i x‖ ≤ ρ) (p : ℕ) :
    ‖∑ i, a i x*b i x^p‖ ≤ Fintype.card ι*A*ρ^p ∧
      ‖deriv (fun t => ∑ i, a i t*b i t^p) x‖ ≤
        Fintype.card ι*(D+A*p*L)*ρ^p := by
  classical
  have hterm := fun i => coefficient_power_norm_bounds (a i) (b i) x (a' i) (b' i)
    (ha i) (hb i) (hb0 i) A D L ρ (hA i) (hD i) (hL i) (hρ i) p
  constructor
  · calc
      _ ≤ ∑ i, ‖a i x*b i x^p‖ := norm_sum_le _ _
      _ ≤ ∑ _i : ι, A*ρ^p := sum_le_sum (fun i _ => (hterm i).1)
      _ = _ := by simp; ring
  · have hd : deriv (fun t => ∑ i, a i t*b i t^p) x =
        ∑ i, deriv (fun t => a i t*b i t^p) x := by
      exact deriv_fun_sum (fun i _ => ((ha i).fun_mul ((hb i).fun_pow p)).differentiableAt)
    rw [hd]
    calc
      _ ≤ ∑ i, ‖deriv (fun t => a i t*b i t^p) x‖ := norm_sum_le _ _
      _ ≤ ∑ _i : ι, (D+A*p*L)*ρ^p := sum_le_sum (fun i _ => (hterm i).2)
      _ = _ := by simp; ring


/-- Compact smooth coefficient families have simultaneous bounds for values,
coefficient derivatives, and logarithmic derivatives of nonzero bases. -/
theorem compact_family_bounds {ι : Type*} [Fintype ι]
    (a b : ι → ℝ → ℂ) (T : ℝ)
    (ha : ∀ i x, x ∈ Icc 0 T → ContDiffAt ℝ ∞ (a i) x)
    (hb : ∀ i x, x ∈ Icc 0 T → ContDiffAt ℝ ∞ (b i) x)
    (hb0 : ∀ i x, x ∈ Icc 0 T → b i x ≠ 0) :
    ∃ A : ℝ, 0<A ∧ ∀ i x, x ∈ Icc 0 T →
      ‖a i x‖ ≤ A ∧ ‖deriv (a i) x‖ ≤ A ∧ ‖deriv (b i) x/b i x‖ ≤ A := by
  classical
  let S : ℝ → ℝ := fun x => ∑ i, (‖a i x‖ + ‖deriv (a i) x‖ + ‖deriv (b i) x/b i x‖)
  have hs0 (x : ℝ) : 0 ≤ S x := by
    exact sum_nonneg (fun i _ => by positivity)
  have hS : ContinuousOn S (Icc 0 T) := by
    apply continuousOn_finsetSum
    intro i _
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have had : ContDiffAt ℝ 0 (deriv (a i)) x := (ha i x hx).derivWithin (by simp)
    have hbd : ContDiffAt ℝ 0 (deriv (b i)) x := (hb i x hx).derivWithin (by simp)
    exact (((ha i x hx).continuousAt.norm.add had.continuousAt.norm).add
      (hbd.continuousAt.div (hb i x hx).continuousAt (hb0 i x hx)).norm)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hS
  refine ⟨max C 0+1, by positivity, ?_⟩
  intro i x hx
  have hsum : ‖a i x‖ + ‖deriv (a i) x‖ + ‖deriv (b i) x/b i x‖ ≤ S x := by
    change _ ≤ ∑ j, (‖a j x‖ + ‖deriv (a j) x‖ + ‖deriv (b j) x/b j x‖)
    exact single_le_sum (f := fun j => ‖a j x‖ + ‖deriv (a j) x‖ + ‖deriv (b j) x/b j x‖) (fun j _ => by positivity) (mem_univ i)
  have hmax := hC x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (hs0 x)] at hmax
  have hCmax : C ≤ max C 0 := le_max_left _ _
  have hn1 := norm_nonneg (a i x)
  have hn2 := norm_nonneg (deriv (a i) x)
  have hn3 := norm_nonneg (deriv (b i) x/b i x)
  constructor
  · linarith
  constructor <;> linarith

/-- The exact uniform error estimates for finite sums of decaying powers.
All constants come from compact smooth families, with no asymptotic premise. -/
theorem uniform_exponential_sum_bounds {ι : Type*} [Fintype ι]
    (a b : ι → ℝ → ℂ) (T c : ℝ)
    (ha : ∀ i x, x ∈ Icc 0 T → ContDiffAt ℝ ∞ (a i) x)
    (hb : ∀ i x, x ∈ Icc 0 T → ContDiffAt ℝ ∞ (b i) x)
    (hb0 : ∀ i x, x ∈ Icc 0 T → b i x ≠ 0)
    (hdecay : ∀ i x, x ∈ Ioc 0 T → ‖b i x‖ ≤ Real.exp (-c*x)) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℕ, ∀ x ∈ Ioc 0 T,
      ‖∑ i, a i x*b i x^p‖ ≤ C*Real.exp (-c*p*x) ∧
      ‖deriv (fun t => ∑ i, a i t*b i t^p) x‖ ≤
        C*(p+1)*Real.exp (-c*p*x) := by
  classical
  obtain ⟨A, hA, hbound⟩ := compact_family_bounds a b T ha hb hb0
  let C : ℝ := Fintype.card ι*(A+A*A)+1
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro p x hx
  have hx' : x ∈ Icc 0 T := ⟨hx.1.le, hx.2⟩
  have h := finite_sum_norm_bounds a b x (fun i => deriv (a i) x)
    (fun i => deriv (b i) x)
    (fun i => ((ha i x hx').differentiableAt (by simp)).hasDerivAt)
    (fun i => ((hb i x hx').differentiableAt (by simp)).hasDerivAt)
    (fun i => hb0 i x hx') A A A (Real.exp (-c*x))
    (fun i => (hbound i x hx').1) (fun i => (hbound i x hx').2.1)
    (fun i => (hbound i x hx').2.2) (fun i => hdecay i x hx) p
  have he : Real.exp (-c*x)^p = Real.exp (-c*p*x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he] at h
  have hcard : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  constructor
  · apply h.1.trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    dsimp [C]
    nlinarith
  · apply h.2.trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    dsimp [C]
    nlinarith [mul_nonneg hcard (mul_nonneg hA.le hA.le),
      mul_nonneg hcard (mul_nonneg hA.le hp)]

end MF21ExpSums
#print axioms MF21ExpSums.finite_sum_norm_bounds
