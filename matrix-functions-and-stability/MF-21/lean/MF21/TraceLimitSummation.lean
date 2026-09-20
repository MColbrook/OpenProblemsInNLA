import MF21.DiscretePowerLimits
import MF21.InverseTraceRecurrence

/-! Summation of polynomially growing increments, for the inverse trace. -/
noncomputable section
open scoped BigOperators Topology
open Filter Finset Asymptotics
namespace MF21DiscreteLimits

/-- The sum of nonnegative integer powers diverges to positive infinity. -/
theorem sum_power_tendsto_atTop (p : ℕ) :
    Tendsto (fun n : ℕ => ∑ k ∈ range n, (k : ℝ) ^ p) atTop atTop := by
  have hp : Tendsto (fun n : ℕ => (n : ℝ) ^ (p+1)) atTop atTop :=
    (tendsto_pow_atTop (by omega : p+1 ≠ 0)).comp tendsto_natCast_atTop_atTop
  have ht := (normalized_power_sum_tendsto p).pos_mul_atTop (by positivity) hp
  apply ht.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  exact div_mul_cancel₀ _ (pow_ne_zero _ hnR)

/-- A limit for normalized increments determines the normalized partial-sum
limit. The assertion is valid for arbitrary signed increments. -/
theorem sum_normalized_tendsto (p : ℕ) (a : ℕ → ℝ) (c : ℝ)
    (ha : Tendsto (fun n => a n / (n : ℝ)^p) atTop (𝓝 c)) :
    Tendsto (fun n => (∑ k ∈ range n, a k) / (n : ℝ)^(p+1))
      atTop (𝓝 (c / (p+1 : ℝ))) := by
  have hne : ∀ᶠ n : ℕ in atTop, (n : ℝ)^p ≠ 0 := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact pow_ne_zero _ (by exact_mod_cast hn)
  have herr : (fun n => a n - c * (n : ℝ)^p) =o[atTop]
      (fun n => (n : ℝ)^p) := by
    apply (isLittleO_iff_tendsto' (hne.mono (fun n hn hz => (hn hz).elim))).mpr
    have ht := ha.sub_const c
    rw [sub_self] at ht
    apply ht.congr'
    filter_upwards [hne] with n hn
    field_simp
  have hsum := herr.sum_range (fun n => pow_nonneg (Nat.cast_nonneg _) _)
    (sum_power_tendsto_atTop p)
  have hbig : (fun n => ∑ k ∈ range n, (k : ℝ)^p) =O[atTop]
      (fun n => (n : ℝ)^(p+1)) := by
    apply isBigO_of_div_tendsto_nhds _ _ (normalized_power_sum_tendsto p)
    filter_upwards [eventually_ne_atTop 0] with n hn hz
    exact (pow_ne_zero (p+1) (by exact_mod_cast hn) hz).elim
  have hz := (hsum.trans_isBigO hbig).tendsto_div_nhds_zero
  have hc := (normalized_power_sum_tendsto p).const_mul c
  have ht := hz.add hc
  simp only [zero_add, ← div_eq_mul_inv] at ht
  apply ht.congr'
  apply Filter.Eventually.of_forall
  intro n
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring


/-- Telescoping version for an arbitrary sequence with polynomial-size
successive increments. -/
theorem sequence_of_increment_tendsto (p : ℕ) (T : ℕ → ℝ) (c : ℝ)
    (h : Tendsto (fun n => (T (n+1) - T n) / (n : ℝ)^p) atTop (𝓝 c)) :
    Tendsto (fun n => T n / (n : ℝ)^(p+1)) atTop (𝓝 (c / (p+1 : ℝ))) := by
  have hs := sum_normalized_tendsto p (fun n => T (n+1)-T n) c h
  have htel (n : ℕ) : (∑ k ∈ range n, (T (k+1) - T k)) = T n - T 0 := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih]; ring
  simp_rw [htel] at hs
  have hp : Tendsto (fun n : ℕ => (n : ℝ) ^ (p+1)) atTop atTop :=
    (tendsto_pow_atTop (by omega : p+1 ≠ 0)).comp tendsto_natCast_atTop_atTop
  have hc := (tendsto_inv_atTop_zero.comp hp).const_mul (T 0)
  simp only [mul_zero] at hc
  have ht := hs.add hc
  simp only [add_zero] at ht
  convert ht using 1
  funext n
  simp only [Function.comp_apply, div_eq_mul_inv]
  ring


/-- Replacing n by n+c in the normalization does not change its limit. -/
theorem normalized_shift_tendsto (p : ℕ) (T : ℕ → ℝ) (a c : ℝ)
    (h : Tendsto (fun n => T n / (n : ℝ)^p) atTop (𝓝 c)) :
    Tendsto (fun n => T n / ((n : ℝ)+a)^p) atTop (𝓝 c) := by
  have ht := h.mul ((tendsto_natCast_div_add_atTop a).pow p)
  simp only [one_pow, mul_one] at ht
  apply ht.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [div_pow]
  field_simp

end MF21DiscreteLimits
#print axioms MF21DiscreteLimits.sum_normalized_tendsto

#print axioms MF21DiscreteLimits.sequence_of_increment_tendsto

#print axioms MF21DiscreteLimits.normalized_shift_tendsto
