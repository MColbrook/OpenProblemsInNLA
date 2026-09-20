import MF21.FirstInverseColumn
import MF21.DiscretePowerLimits
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.SpecificLimits.Basic

/-! Polynomial rescaling of the exact first inverse column. -/

noncomputable section
open Polynomial Finset Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency.types false

namespace MF21FirstAsymptotics

/-- Numerator after dividing the kth inverse entry by n^r, with x=k/n, t=1/n. -/
def numerator (r : ℕ) (t : ℝ) : ℝ[X] :=
  (∏ a ∈ range r, (X + C (((a : ℝ) + 1) * t))) *
    (∏ b ∈ range (r + 1), (C (1 + (b : ℝ) * t) - X))

def denominator (r : ℕ) (t : ℝ) : ℝ :=
  (r.factorial : ℝ) * ∏ c ∈ range (r + 1), (1 + ((r : ℝ) + 1 + c) * t)

theorem asc_eval_prod (q : ℕ) (x : ℝ) :
    (ascPochhammer ℝ q).eval x = ∏ j ∈ range q, (x + (j : ℝ)) := by
  induction q with
  | zero => simp
  | succ q ih => rw [ascPochhammer_succ_eval, prod_range_succ, ih]

theorem asc_eval_rescale (q : ℕ) (x N : ℝ) (hN : N ≠ 0) :
    (ascPochhammer ℝ q).eval x =
      N ^ q * ∏ j ∈ range q, (x / N + (j : ℝ) / N) := by
  rw [asc_eval_prod]
  calc
    (∏ j ∈ range q, (x + (j : ℝ))) =
        ∏ j ∈ range q, N * (x / N + (j : ℝ) / N) := by
      apply prod_congr rfl
      intro j hj
      field_simp
    _ = _ := by rw [prod_mul_distrib]; simp

theorem numerator_eval (r : ℕ) (t x : ℝ) :
    (numerator r t).eval x =
      (∏ a ∈ range r, (x + ((a : ℝ) + 1) * t)) *
        (∏ b ∈ range (r + 1), (1 - x + (b : ℝ) * t)) := by
  simp only [numerator, eval_mul, eval_prod, eval_add, eval_X, eval_C, eval_sub]
  congr 1
  apply prod_congr rfl
  intro b hb
  ring

theorem denominator_pos (r : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    0 < denominator r t := by
  unfold denominator
  apply mul_pos (by exact_mod_cast Nat.factorial_pos r)
  apply prod_pos
  intro c hc
  positivity

/-- Exact rescaling identity, valid for every real evaluation point k. -/
theorem value_rescaled (r n : ℕ) (hn : 0 < n) (k : ℝ) :
    MF21FirstColumn.value r n k / (n : ℝ) ^ r =
      (numerator r (n : ℝ)⁻¹).eval (k / (n : ℝ)) /
        denominator r (n : ℝ)⁻¹ := by
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hfac : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  rw [MF21FirstColumn.value_formula]
  unfold MF21FirstColumn.normalizer
  rw [asc_eval_rescale r (k + 1) (n : ℝ) hN,
    asc_eval_rescale (r + 1) ((n : ℝ) - k) (n : ℝ) hN,
    asc_eval_rescale (r + 1) ((n : ℝ) + (r + 1)) (n : ℝ) hN,
    numerator_eval]
  have hleft : (∏ a ∈ range r, ((k + 1) / (n : ℝ) + (a : ℝ) / n)) =
      ∏ a ∈ range r, (k / (n : ℝ) + ((a : ℝ) + 1) * (n : ℝ)⁻¹) := by
    apply prod_congr rfl
    intro a ha
    ring
  have hright : (∏ b ∈ range (r + 1),
        (((n : ℝ) - k) / (n : ℝ) + (b : ℝ) / n)) =
      ∏ b ∈ range (r + 1), (1 - k / (n : ℝ) + (b : ℝ) * (n : ℝ)⁻¹) := by
    apply prod_congr rfl
    intro b hb
    field_simp
  have hden : (∏ c ∈ range (r + 1),
        (((n : ℝ) + (r + 1)) / (n : ℝ) + (c : ℝ) / n)) =
      ∏ c ∈ range (r + 1), (1 + ((r : ℝ) + 1 + c) * (n : ℝ)⁻¹) := by
    apply prod_congr rfl
    intro c hc
    field_simp
    ring
  rw [hleft, hright, hden]
  unfold denominator
  field_simp

/-- Continuity of all coefficients of a polynomial family. -/
def CoeffContinuous (P : ℝ → ℝ[X]) : Prop :=
  ∀ i, Continuous (fun t ↦ (P t).coeff i)

theorem coeffContinuous_const (p : ℝ[X]) : CoeffContinuous (fun _ ↦ p) :=
  fun _ ↦ continuous_const

theorem coeffContinuous_C (f : ℝ → ℝ) (hf : Continuous f) :
    CoeffContinuous (fun t ↦ C (f t)) := by
  intro i
  simp only [coeff_C]
  by_cases hi : i = 0
  · simpa [hi] using hf
  · simpa [hi] using (continuous_const : Continuous (fun _ : ℝ ↦ (0 : ℝ)))

theorem coeffContinuous_add (P Q : ℝ → ℝ[X])
    (hP : CoeffContinuous P) (hQ : CoeffContinuous Q) :
    CoeffContinuous (fun t ↦ P t + Q t) := by
  intro i
  simp only [coeff_add]
  have hP' := hP i
  have hQ' := hQ i
  fun_prop

theorem coeffContinuous_sub (P Q : ℝ → ℝ[X])
    (hP : CoeffContinuous P) (hQ : CoeffContinuous Q) :
    CoeffContinuous (fun t ↦ P t - Q t) := by
  intro i
  simp only [coeff_sub]
  have hP' := hP i
  have hQ' := hQ i
  fun_prop

theorem coeffContinuous_mul (P Q : ℝ → ℝ[X])
    (hP : CoeffContinuous P) (hQ : CoeffContinuous Q) :
    CoeffContinuous (fun t ↦ P t * Q t) := by
  intro i
  simp only [coeff_mul]
  exact continuous_finsetSum _ (fun ab _ ↦ (hP ab.1).mul (hQ ab.2))

theorem coeffContinuous_prod {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ[X])
    (hF : ∀ i ∈ s, CoeffContinuous (F i)) :
    CoeffContinuous (fun t ↦ ∏ i ∈ s, F i t) := by
  classical
  induction s using Finset.induction with
  | empty => simpa only [prod_empty] using coeffContinuous_const 1
  | @insert a s ha ih =>
    simp only [prod_insert ha]
    exact coeffContinuous_mul _ _ (hF a (mem_insert_self _ _))
      (ih (fun i hi ↦ hF i (mem_insert_of_mem hi)))

theorem numerator_coeff_continuous (r : ℕ) : CoeffContinuous (numerator r) := by
  apply coeffContinuous_mul
  · apply coeffContinuous_prod
    intro a ha
    exact coeffContinuous_add _ _ (coeffContinuous_const X)
      (coeffContinuous_C _ (continuous_const.mul continuous_id))
  · apply coeffContinuous_prod
    intro b hb
    exact coeffContinuous_sub _ _
      (coeffContinuous_C _ (continuous_const.add (continuous_const.mul continuous_id)))
      (coeffContinuous_const X)

theorem numerator_zero (r : ℕ) : numerator r 0 = X ^ r * (1 - X) ^ (r + 1) := by
  simp [numerator]

theorem denominator_zero (r : ℕ) : denominator r 0 = (r.factorial : ℝ) := by
  simp [denominator]

theorem denominator_continuous (r : ℕ) : Continuous (denominator r) := by
  unfold denominator
  apply continuous_const.mul
  exact continuous_finsetProd _ (fun c _ ↦
    continuous_const.add (continuous_const.mul continuous_id))

theorem numerator_degree (r : ℕ) (t : ℝ) :
    (numerator r t).natDegree ≤ 2 * r + 1 := by
  have hleft : (∏ a ∈ range r, (X + C (((a : ℝ) + 1) * t))).natDegree ≤ r := by
    calc
      _ ≤ ∑ a ∈ range r, (X + C (((a : ℝ) + 1) * t)).natDegree :=
        natDegree_prod_le _ _
      _ = r := by simp only [natDegree_X_add_C, sum_const, card_range, smul_eq_mul, mul_one]
  have hCX (a : ℝ) : (C a - X).natDegree = 1 := by
    rw [← natDegree_neg]
    simp only [neg_sub, natDegree_X_sub_C]
  have hright : (∏ b ∈ range (r + 1), (C (1 + (b : ℝ) * t) - X)).natDegree ≤ r + 1 := by
    calc
      _ ≤ ∑ b ∈ range (r + 1), (C (1 + (b : ℝ) * t) - X).natDegree :=
        natDegree_prod_le _ _
      _ = r + 1 := by simp only [hCX, sum_const, card_range, smul_eq_mul, mul_one]
  unfold numerator
  exact (natDegree_mul_le).trans (by omega)

theorem numerator_square_degree (r : ℕ) (t : ℝ) :
    ((numerator r t) ^ 2).natDegree < 4 * r + 3 := by
  have := natDegree_pow_le (p := numerator r t) (n := 2)
  have := numerator_degree r t
  omega

theorem inverse_dimension_tendsto :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

theorem numerator_square_coeff_continuous (r : ℕ) :
    CoeffContinuous (fun t ↦ (numerator r t) ^ 2) := by
  simpa only [pow_two] using
    coeffContinuous_mul _ _ (numerator_coeff_continuous r) (numerator_coeff_continuous r)

theorem numerator_square_riemann_tendsto (r : ℕ) :
    Tendsto (fun n : ℕ ↦
      (∑ j ∈ range n, ((numerator r (n : ℝ)⁻¹) ^ 2).eval ((j : ℝ) / n)) / n)
      atTop (𝓝 (∫ x in (0 : ℝ)..1, ((numerator r 0) ^ 2).eval x)) := by
  apply MF21DiscreteLimits.polynomial_riemann_tendsto (4 * r + 3)
  · exact fun n ↦ numerator_square_degree r _
  · exact numerator_square_degree r 0
  · intro i hi
    exact ((numerator_square_coeff_continuous r i).tendsto 0).comp inverse_dimension_tendsto

/-- The limiting squared norm of the actual finite inverse-column formula. -/
theorem firstColumn_square_sum_tendsto (r : ℕ) :
    Tendsto (fun n : ℕ ↦
      (∑ j ∈ range n, (MF21FirstColumn.value r n (j : ℝ)) ^ 2) /
        (n : ℝ) ^ (2 * r + 1)) atTop
      (𝓝 ((∫ x in (0 : ℝ)..1, x ^ (2 * r) * (1 - x) ^ (2 * r + 2)) /
        (r.factorial : ℝ) ^ 2)) := by
  have hden : Tendsto (fun n : ℕ ↦ denominator r (n : ℝ)⁻¹)
      atTop (𝓝 (r.factorial : ℝ)) := by
    simpa only [denominator_zero, Function.comp_def] using
      ((denominator_continuous r).tendsto 0).comp inverse_dimension_tendsto
  have hfac : (r.factorial : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (by
    exact_mod_cast Nat.factorial_ne_zero r)
  have ht := (numerator_square_riemann_tendsto r).div (hden.pow 2) hfac
  have heval (x : ℝ) : ((numerator r 0) ^ 2).eval x =
      x ^ (2 * r) * (1 - x) ^ (2 * r + 2) := by
    rw [numerator_zero]
    simp only [eval_pow, eval_mul, eval_sub, eval_one, eval_X, mul_pow, ← pow_mul]
    congr 1 <;> congr 1 <;> omega
  simp_rw [heval] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hterm (j : ℕ) :
      ((numerator r (n : ℝ)⁻¹) ^ 2).eval ((j : ℝ) / n) /
          (denominator r (n : ℝ)⁻¹) ^ 2 =
        (MF21FirstColumn.value r n (j : ℝ)) ^ 2 / (n : ℝ) ^ (2 * r) := by
    rw [eval_pow, ← div_pow, ← value_rescaled r n hn (j : ℝ), div_pow, ← pow_mul]
    rw [Nat.mul_comm r 2]
  change ((∑ j ∈ range n, ((numerator r (n : ℝ)⁻¹) ^ 2).eval ((j : ℝ) / n)) / n) /
    (denominator r (n : ℝ)⁻¹) ^ 2 = _
  rw [div_right_comm, sum_div]
  simp_rw [hterm]
  rw [← sum_div, div_div, ← pow_succ]

theorem asc_eval_shift_rescale (q : ℕ) (a N : ℝ) (hN : N ≠ 0) :
    (ascPochhammer ℝ q).eval (N + a) =
      N ^ q * ∏ j ∈ range q, (1 + (a + j) * N⁻¹) := by
  rw [asc_eval_rescale q (N + a) N hN]
  congr 1
  apply prod_congr rfl
  intro j hj
  field_simp
  ring

theorem value_zero_rescaled (r n : ℕ) (hn : 0 < n) :
    MF21FirstColumn.value r n 0 =
      (r.factorial : ℝ) * (∏ b ∈ range (r + 1), (1 + (b : ℝ) * (n : ℝ)⁻¹)) /
        denominator r (n : ℝ)⁻¹ := by
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [MF21FirstColumn.value_formula]
  simp only [zero_add, sub_zero, ascPochhammer_eval_one]
  unfold MF21FirstColumn.normalizer
  rw [asc_eval_shift_rescale (r + 1) ((r : ℝ) + 1) (n : ℝ) hN]
  have hnum := asc_eval_shift_rescale (r + 1) 0 (n : ℝ) hN
  simp only [add_zero, zero_add] at hnum
  rw [hnum]
  unfold denominator
  field_simp

theorem value_zero_tendsto (r : ℕ) :
    Tendsto (fun n : ℕ ↦ MF21FirstColumn.value r n 0) atTop (𝓝 (1 : ℝ)) := by
  have hnum : Tendsto (fun n : ℕ ↦
      ∏ b ∈ range (r + 1), (1 + (b : ℝ) * (n : ℝ)⁻¹)) atTop (𝓝 (1 : ℝ)) := by
    have hc : Continuous (fun t : ℝ ↦ ∏ b ∈ range (r + 1), (1 + (b : ℝ) * t)) :=
      continuous_finsetProd _ (fun b _ ↦
        continuous_const.add (continuous_const.mul continuous_id))
    simpa [Function.comp_def] using (hc.tendsto 0).comp inverse_dimension_tendsto
  have hden : Tendsto (fun n : ℕ ↦ denominator r (n : ℝ)⁻¹)
      atTop (𝓝 (r.factorial : ℝ)) := by
    simpa only [denominator_zero, Function.comp_def] using
      ((denominator_continuous r).tendsto 0).comp inverse_dimension_tendsto
  have hfac : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have ht := (hnum.const_mul (r.factorial : ℝ)).div hden hfac
  change Tendsto (fun n : ℕ ↦
      (r.factorial : ℝ) * (∏ b ∈ range (r + 1), (1 + (b : ℝ) * (n : ℝ)⁻¹)) /
        denominator r (n : ℝ)⁻¹) atTop (𝓝 ((r.factorial : ℝ) * 1 / r.factorial)) at ht
  have ht' : Tendsto (fun n : ℕ ↦
      (r.factorial : ℝ) * (∏ b ∈ range (r + 1), (1 + (b : ℝ) * (n : ℝ)⁻¹)) /
        denominator r (n : ℝ)⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa [hfac, Pi.mul_apply, Pi.div_apply] using ht
  apply ht'.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (value_zero_rescaled r n hn).symm

/-- Squared norm limit for the actual inverse of the Toeplitz matrix. -/
theorem inverse_column_square_sum_tendsto (r : ℕ) :
    Tendsto (fun n : ℕ ↦
      (∑ j : Fin (n + 1), (((MF21Challenge.toeplitz (r + 1) (n + 1))⁻¹) j 0) ^ 2) /
        ((n + 1 : ℕ) : ℝ) ^ (2 * r + 1)) atTop
      (𝓝 ((∫ x in (0 : ℝ)..1, x ^ (2 * r) * (1 - x) ^ (2 * r + 2)) /
        (r.factorial : ℝ) ^ 2)) := by
  have ht := (firstColumn_square_sum_tendsto r).comp (tendsto_add_atTop_nat 1)
  convert ht using 1
  funext n
  simp only [Function.comp_apply, MF21FirstColumn.inverse_column_eq,
    MF21FirstColumn.firstColumn]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun j ↦ MF21FirstColumn.value r (n + 1) (j : ℝ) ^ 2) (n + 1)

theorem inverse_zero_zero_tendsto (r : ℕ) :
    Tendsto (fun n : ℕ ↦ ((MF21Challenge.toeplitz (r + 1) (n + 1))⁻¹) 0 0)
      atTop (𝓝 (1 : ℝ)) := by
  have ht := (value_zero_tendsto r).comp (tendsto_add_atTop_nat 1)
  convert ht using 1
  funext n
  simp only [Function.comp_apply, MF21FirstColumn.inverse_column_eq,
    MF21FirstColumn.firstColumn, Fin.val_zero, Nat.cast_zero]

end MF21FirstAsymptotics

#print axioms MF21FirstAsymptotics.value_rescaled
#print axioms MF21FirstAsymptotics.numerator_coeff_continuous

#print axioms MF21FirstAsymptotics.firstColumn_square_sum_tendsto
#print axioms MF21FirstAsymptotics.inverse_column_square_sum_tendsto
#print axioms MF21FirstAsymptotics.inverse_zero_zero_tendsto
