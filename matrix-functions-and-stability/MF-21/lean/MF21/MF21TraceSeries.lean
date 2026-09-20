import MF21.MF21Transcendence
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! Exact shifted even-zeta tails for the MF-21 comparison trace. -/

noncomputable section
open Finset

namespace MF21Audit

/-- Rational coefficient in Euler's even-zeta formula. -/
def evenZetaCoefficient (m : ℕ) : ℚ :=
  (-1) ^ (m + 1) * 2 ^ (2 * m - 1) * bernoulli (2 * m) / (2 * m).factorial

def integerCorrection (m r : ℕ) : ℚ :=
  ∑ k ∈ range (r + 1), 1 / (k : ℚ) ^ (2 * m)

def halfCorrection (m r : ℕ) : ℚ :=
  ∑ k ∈ range r, 1 / ((k : ℚ) + 1 / 2) ^ (2 * m)

/-- The exact infinite series that appears as the hypothetical MF-21 trace. -/
def modelTrace (m : ℕ) : ℝ :=
  (Real.pi ^ (2 * m))⁻¹ *
    ∑' j : ℕ, 1 / ((j : ℝ) + 1 + ((m : ℝ) - 1) / 2) ^ (2 * m)

/-- The exact rational number calculated from the Green-kernel diagonal. -/
def kernelTraceConstant (m : ℕ) : ℚ :=
  ((2 * m - 1).factorial : ℚ) ^ 2 /
    (((4 * m - 1).factorial : ℚ) * (2 * m - 1 : ℕ) *
      ((m - 1).factorial : ℚ) ^ 2)

theorem even_zeta_sum (m : ℕ) (hm : 0 < m) :
    (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * m)) =
      (evenZetaCoefficient m : ℝ) * Real.pi ^ (2 * m) := by
  rw [(hasSum_zeta_nat (Nat.ne_of_gt hm)).tsum_eq]
  simp only [evenZetaCoefficient, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast]
  ring

theorem integer_tail_sum (m r : ℕ) (hm : 0 < m) :
    (∑' j : ℕ, 1 / ((j : ℝ) + r + 1) ^ (2 * m)) =
      (evenZetaCoefficient m : ℝ) * Real.pi ^ (2 * m) -
        (integerCorrection m r : ℝ) := by
  have h := Summable.sum_add_tsum_nat_add (r + 1)
    (hasSum_zeta_nat (Nat.ne_of_gt hm)).summable
  have hc : (integerCorrection m r : ℝ) =
      ∑ k ∈ range (r + 1), 1 / (k : ℝ) ^ (2 * m) := by
    simp [integerCorrection]
  have ht : (∑' j : ℕ, 1 / ((j : ℝ) + r + 1) ^ (2 * m)) =
      ∑' j : ℕ, 1 / ((j + (r + 1) : ℕ) : ℝ) ^ (2 * m) := by
    congr 1
    ext j
    simp [Nat.cast_add, add_assoc]
  rw [even_zeta_sum m hm, ← hc, ← ht] at h
  linarith

theorem integerCorrection_pos (m r : ℕ) (hr : 0 < r) :
    0 < integerCorrection m r := by
  unfold integerCorrection
  apply Finset.sum_pos'
  · intro k hk
    positivity
  · exact ⟨1, by simp [hr], by norm_num⟩

theorem halfCorrection_pos (m r : ℕ) (hr : 0 < r) :
    0 < halfCorrection m r := by
  unfold halfCorrection
  apply Finset.sum_pos'
  · intro k hk
    positivity
  · exact ⟨0, by simpa using hr, by positivity⟩

theorem half_term_eq_odd_term (s j : ℕ) :
    1 / ((j : ℝ) + 1 / 2) ^ s =
      (2 : ℝ) ^ s * (1 / ((2 * j + 1 : ℕ) : ℝ) ^ s) := by
  have heq : (j : ℝ) + 1 / 2 = ((2 * j + 1 : ℕ) : ℝ) / 2 := by
    push_cast
    ring
  rw [heq, div_pow]
  simp [div_eq_mul_inv, mul_comm]

theorem half_sequence_summable (m : ℕ) (hm : 0 < m) :
    Summable (fun j : ℕ ↦ 1 / ((j : ℝ) + 1 / 2) ^ (2 * m)) := by
  have ho := (hasSum_zeta_nat (Nat.ne_of_gt hm)).summable.comp_injective
    (i := fun j : ℕ ↦ 2 * j + 1) (by intro i j h; dsimp at h; omega)
  simpa only [Function.comp_apply, half_term_eq_odd_term] using
    ho.mul_left ((2 : ℝ) ^ (2 * m))

theorem half_sequence_sum (m : ℕ) (hm : 0 < m) :
    (∑' j : ℕ, 1 / ((j : ℝ) + 1 / 2) ^ (2 * m)) =
      ((2 : ℝ) ^ (2 * m) - 1) *
        ((evenZetaCoefficient m : ℝ) * Real.pi ^ (2 * m)) := by
  have hz := (hasSum_zeta_nat (Nat.ne_of_gt hm)).summable
  have he := hz.comp_injective (i := fun j : ℕ ↦ 2 * j)
    (by intro i j h; dsimp at h; omega)
  have ho := hz.comp_injective (i := fun j : ℕ ↦ 2 * j + 1)
    (by intro i j h; dsimp at h; omega)
  have hs := tsum_even_add_odd (f := fun k : ℕ ↦ 1 / (k : ℝ) ^ (2 * m)) he ho
  have heq : (∑' j : ℕ, 1 / ((2 * j : ℕ) : ℝ) ^ (2 * m)) =
      (∑' j : ℕ, 1 / (j : ℝ) ^ (2 * m)) / (2 : ℝ) ^ (2 * m) := by
    rw [← tsum_div_const]
    apply tsum_congr
    intro j
    simp [Nat.cast_mul, mul_pow, div_eq_mul_inv, mul_comm]
  rw [heq, even_zeta_sum m hm] at hs
  simp_rw [half_term_eq_odd_term]
  rw [tsum_mul_left]
  generalize hZ : (evenZetaCoefficient m : ℝ) * Real.pi ^ (2 * m) = Z at hs ⊢
  generalize hT : (2 : ℝ) ^ (2 * m) = T at hs ⊢
  have ht : T ≠ 0 := by rw [← hT]; positivity
  field_simp [ht] at hs
  nlinarith only [hs]

theorem half_tail_sum (m r : ℕ) (hm : 0 < m) :
    (∑' j : ℕ, 1 / ((j : ℝ) + r + 1 / 2) ^ (2 * m)) =
      ((2 : ℝ) ^ (2 * m) - 1) *
        ((evenZetaCoefficient m : ℝ) * Real.pi ^ (2 * m)) -
          (halfCorrection m r : ℝ) := by
  have h := Summable.sum_add_tsum_nat_add r (half_sequence_summable m hm)
  have hc : (halfCorrection m r : ℝ) =
      ∑ k ∈ range r, 1 / ((k : ℝ) + 1 / 2) ^ (2 * m) := by
    simp [halfCorrection]
  have ht : (∑' j : ℕ, 1 / ((j : ℝ) + r + 1 / 2) ^ (2 * m)) =
      ∑' j : ℕ, 1 / (((j + r : ℕ) : ℝ) + 1 / 2) ^ (2 * m) := by
    congr 1
    ext j
    simp
  rw [half_sequence_sum m hm, ← hc, ← ht] at h
  linarith

theorem integer_tail_normalized (m r : ℕ) (hm : 0 < m) :
    (Real.pi ^ (2 * m))⁻¹ *
      (∑' j : ℕ, 1 / ((j : ℝ) + r + 1) ^ (2 * m)) =
        (evenZetaCoefficient m : ℝ) -
          (integerCorrection m r : ℝ) / Real.pi ^ (2 * m) := by
  rw [integer_tail_sum m r hm]
  have hp : Real.pi ^ (2 * m) ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  field_simp

theorem half_tail_normalized (m r : ℕ) (hm : 0 < m) :
    (Real.pi ^ (2 * m))⁻¹ *
      (∑' j : ℕ, 1 / ((j : ℝ) + r + 1 / 2) ^ (2 * m)) =
        (((2 : ℚ) ^ (2 * m) - 1) * evenZetaCoefficient m : ℚ) -
          (halfCorrection m r : ℝ) / Real.pi ^ (2 * m) := by
  rw [half_tail_sum m r hm]
  push_cast
  have hp : Real.pi ^ (2 * m) ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  field_simp

theorem integer_tail_irrational (m r : ℕ) (hm : 0 < m) (hr : 0 < r) :
    Irrational ((Real.pi ^ (2 * m))⁻¹ *
      (∑' j : ℕ, 1 / ((j : ℝ) + r + 1) ^ (2 * m))) := by
  rw [integer_tail_normalized m r hm]
  exact pi_trace_value_irrational (evenZetaCoefficient m) (integerCorrection m r)
    (ne_of_gt (integerCorrection_pos m r hr)) (2 * m) (by omega)

theorem half_tail_irrational (m r : ℕ) (hm : 0 < m) (hr : 0 < r) :
    Irrational ((Real.pi ^ (2 * m))⁻¹ *
      (∑' j : ℕ, 1 / ((j : ℝ) + r + 1 / 2) ^ (2 * m))) := by
  rw [half_tail_normalized m r hm]
  exact pi_trace_value_irrational (((2 : ℚ) ^ (2 * m) - 1) * evenZetaCoefficient m)
    (halfCorrection m r) (ne_of_gt (halfCorrection_pos m r hr)) (2 * m) (by omega)

/-- The comparison trace is irrational for every source parameter m ≥ 3,
with its actual infinite series and no auxiliary arithmetic hypotheses. -/
theorem modelTrace_irrational (m : ℕ) (hm : 3 ≤ m) : Irrational (modelTrace m) := by
  obtain ⟨r, heven | hodd⟩ := Nat.even_or_odd' m
  · subst m
    have heq : modelTrace (2 * r) =
        (Real.pi ^ (2 * (2 * r)))⁻¹ *
          (∑' j : ℕ, 1 / ((j : ℝ) + r + 1 / 2) ^ (2 * (2 * r))) := by
      unfold modelTrace
      congr 1
      apply tsum_congr
      intro j
      congr 2
      push_cast
      ring
    rw [heq]
    exact half_tail_irrational (2 * r) r (by omega) (by omega)
  · subst m
    have heq : modelTrace (2 * r + 1) =
        (Real.pi ^ (2 * (2 * r + 1)))⁻¹ *
          (∑' j : ℕ, 1 / ((j : ℝ) + r + 1) ^ (2 * (2 * r + 1))) := by
      unfold modelTrace
      congr 1
      apply tsum_congr
      intro j
      congr 2
      push_cast
      ring
    rw [heq]
    exact integer_tail_irrational (2 * r + 1) r (by omega) (by omega)

/-- The actual rational Green-kernel constant cannot equal the model series. -/
theorem kernelTraceConstant_ne_modelTrace (m : ℕ) (hm : 3 ≤ m) :
    (kernelTraceConstant m : ℝ) ≠ modelTrace m := by
  intro heq
  exact modelTrace_irrational m hm ⟨kernelTraceConstant m, heq⟩

/-- Summability of the comparison eigenvalue reciprocals in the source indexing. -/
theorem modelTrace_series_summable (m : ℕ) (hm : 3 ≤ m) :
    Summable (fun j : ℕ ↦
      1 / ((j : ℝ) + 1 + ((m : ℝ) - 1) / 2) ^ (2 * m)) := by
  have hmr : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hshift : 0 ≤ ((m : ℝ) - 1) / 2 := by linarith
  have hbase : Summable (fun j : ℕ ↦ 1 / ((j : ℝ) + 1) ^ (2 * m)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (hasSum_zeta_nat (by omega : m ≠ 0)).summable
  apply Summable.of_nonneg_of_le (fun j ↦ by positivity) _ hbase
  intro j
  gcongr <;> linarith

end MF21Audit

#print axioms MF21Audit.even_zeta_sum
#print axioms MF21Audit.half_tail_sum
#print axioms MF21Audit.modelTrace_irrational
#print axioms MF21Audit.kernelTraceConstant_ne_modelTrace
#print axioms MF21Audit.modelTrace_series_summable
