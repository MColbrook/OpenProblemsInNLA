import MF21Restart.InverseSpectralTrace
import MF21Restart.TraceSeriesZeta
import Mathlib.Analysis.Normed.Group.Tannery

/-! The dominated spectral trace passage (31), conditional on the actual
fixed-index limits and the explicit j>=2 reciprocal majorant from (22).
No trace convergence is assumed. Prior lock:
SPECTRAL_TRACE_PASSAGE_STATEMENTS.md. -/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Topology

namespace MF21Restart

/-- Zero-based counting index k corresponds to the original index k+1. -/
def inverseSpectralTerm (m n k : ℕ) : ℝ :=
  if k < n then
    (1 / (n + 2 : ℝ)) ^ (2 * m) / eigenvalue m n (k + 1)
  else 0

theorem inverseSpectralTerm_nonneg (m : ℕ) (hm : 1 ≤ m) (n k : ℕ) :
    0 ≤ inverseSpectralTerm m n k := by
  unfold inverseSpectralTerm
  split_ifs with hk
  · exact div_nonneg (pow_nonneg (by positivity) _)
      (eigenvalue_strict_spectral_enclosure m n (k + 1) hm (by omega) (by omega)).1.le
  · exact le_rfl

/-- The whole finite spectrum is present: k=0 is j=1, and k=n-1 is j=n. -/
theorem tsum_inverseSpectralTerm_eq_trace (m n : ℕ) (hm : 1 ≤ m) :
    (∑' k : ℕ, inverseSpectralTerm m n k) =
      (1 / (n + 2 : ℝ)) ^ (2 * m) * Matrix.trace (toeplitz m n)⁻¹ := by
  classical
  rw [tsum_eq_sum (s := Finset.range n) (fun k hk => by
    have hkn : ¬k < n := by simpa only [Finset.mem_range] using hk
    simp only [inverseSpectralTerm, if_neg hkn])]
  calc
    (∑ k ∈ Finset.range n, inverseSpectralTerm m n k) =
        ∑ k ∈ Finset.range n, (1 / (n + 2 : ℝ)) ^ (2 * m) /
          eigenvalue m n (k + 1) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [inverseSpectralTerm, if_pos (Finset.mem_range.mp hk)]
    _ = ∑ i : Fin n, (1 / (n + 2 : ℝ)) ^ (2 * m) /
        eigenvalue m n (i.val + 1) :=
      (Fin.sum_univ_eq_sum_range
        (fun k => (1 / (n + 2 : ℝ)) ^ (2 * m) / eigenvalue m n (k + 1)) n).symm
    _ = (1 / (n + 2 : ℝ)) ^ (2 * m) *
        ∑ i : Fin n, 1 / eigenvalue m n (i.val + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [toeplitz_inverse_trace_one_based m n hm]

/-- Inversion of the strictly positive fixed-index spectral limit. -/
theorem inverseSpectralTerm_tendsto
    (m : ℕ) (hm : 1 ≤ m)
    (hfixed : ∀ j : ℕ, 1 ≤ j →
      Tendsto (fun n : ℕ => (n + 2 : ℝ) ^ (2 * m) * eigenvalue m n j)
        atTop (𝓝 (Real.pi ^ (2 * m) *
          ((j : ℝ) + ((m - 1 : ℕ) : ℝ) / 2) ^ (2 * m)))) :
    ∀ k : ℕ, Tendsto (fun n => inverseSpectralTerm m n k) atTop
      (𝓝 ((Real.pi ^ (2 * m))⁻¹ *
        (((k : ℝ) + 1 + ((m - 1 : ℕ) : ℝ) / 2) ^ (2 * m))⁻¹)) := by
  intro k
  have hpositive : 0 < Real.pi ^ (2 * m) *
      (((k + 1 : ℕ) : ℝ) + ((m - 1 : ℕ) : ℝ) / 2) ^ (2 * m) := by
    have hkpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hshift : (0 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) / 2 := by positivity
    exact mul_pos (pow_pos Real.pi_pos _) (pow_pos (by linarith) _)
  have hinv := (hfixed (k + 1) (by omega)).inv₀ hpositive.ne'
  have hinv' : Tendsto
      (fun n : ℕ => ((n + 2 : ℝ) ^ (2 * m) * eigenvalue m n (k + 1))⁻¹)
      atTop (𝓝 ((Real.pi ^ (2 * m))⁻¹ *
        (((k : ℝ) + 1 + ((m - 1 : ℕ) : ℝ) / 2) ^ (2 * m))⁻¹)) := by
    simpa only [Nat.cast_add, Nat.cast_one, mul_inv_rev, mul_comm] using hinv
  have heq : (fun n => inverseSpectralTerm m n k) =ᶠ[atTop]
      (fun n : ℕ => ((n + 2 : ℝ) ^ (2 * m) * eigenvalue m n (k + 1))⁻¹) := by
    filter_upwards [eventually_ge_atTop (k + 1)] with n hn
    rw [inverseSpectralTerm, if_pos (by omega : k < n)]
    simp only [one_div_pow, one_div, div_eq_mul_inv, mul_inv_rev]
    ring
  exact hinv'.congr' heq.symm

/-- The first reciprocal term is controlled by its own limit. The
summable tail bound applies only to original indices j>=2, as in (22). -/
theorem toeplitz_inverse_trace_tendsto_series_of_limits_and_majorant
    (m : ℕ) (hm : 1 ≤ m)
    (hfixed : ∀ j : ℕ, 1 ≤ j →
      Tendsto (fun n : ℕ => (n + 2 : ℝ) ^ (2 * m) * eigenvalue m n j)
        atTop (𝓝 (Real.pi ^ (2 * m) *
          ((j : ℝ) + ((m - 1 : ℕ) : ℝ) / 2) ^ (2 * m))))
    (hmajorant : ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 2 ≤ j → j ≤ n →
        (1 / (n + 2 : ℝ)) ^ (2 * m) / eigenvalue m n j ≤
          C * ((j : ℝ) ^ (2 * m))⁻¹) :
    Tendsto (fun n : ℕ =>
      (1 / (n + 2 : ℝ)) ^ (2 * m) * Matrix.trace (toeplitz m n)⁻¹)
      atTop (𝓝 ((Real.pi ^ (2 * m))⁻¹ *
        ∑' k : ℕ,
          (((k : ℝ) + 1 + ((m - 1 : ℕ) : ℝ) / 2) ^ (2 * m))⁻¹)) := by
  classical
  obtain ⟨C, hC, N, hmajor⟩ := hmajorant
  let L : ℝ := (Real.pi ^ (2 * m))⁻¹ *
    (((0 : ℝ) + 1 + ((m - 1 : ℕ) : ℝ) / 2) ^ (2 * m))⁻¹
  let D : ℝ := ‖L‖ + 1
  have hD : 0 < D := by dsimp only [D]; positivity
  have hfirst : Tendsto (fun n => inverseSpectralTerm m n 0) atTop (𝓝 L) := by
    simpa only [L, Nat.cast_zero] using inverseSpectralTerm_tendsto m hm hfixed 0
  have hfirstBound : ∀ᶠ n : ℕ in atTop, ‖inverseSpectralTerm m n 0‖ < D :=
    (tendsto_order.mp hfirst.norm).2 D (by dsimp only [D]; linarith)
  let bound : ℕ → ℝ := fun k =>
    C * (((k : ℝ) + 1) ^ (2 * m))⁻¹ + if k = 0 then D else 0
  have hsum : Summable bound := by
    exact ((hasSum_even_zeta_positive m hm).summable.mul_left C).add
      (hasSum_ite_eq (0 : ℕ) D).summable
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, ‖inverseSpectralTerm m n k‖ ≤ bound k := by
    filter_upwards [eventually_ge_atTop N, hfirstBound] with n hn hfirstn
    intro k
    by_cases hk0 : k = 0
    · subst k
      calc
        ‖inverseSpectralTerm m n 0‖ ≤ D := hfirstn.le
        _ ≤ bound 0 := by
          dsimp only [bound]
          simp only [if_true, Nat.cast_zero, zero_add, one_pow, inv_one, mul_one]
          linarith
    · by_cases hkn : k < n
      · rw [Real.norm_eq_abs, abs_of_nonneg (inverseSpectralTerm_nonneg m hm n k),
          inverseSpectralTerm, if_pos hkn]
        have hb := hmajor n hn (k + 1) (by omega) (by omega)
        simpa only [bound, if_neg hk0, add_zero, Nat.cast_add, Nat.cast_one] using hb
      · simp only [inverseSpectralTerm, if_neg hkn, norm_zero]
        dsimp only [bound]
        rw [if_neg hk0, add_zero]
        positivity
  have hlim := tendsto_tsum_of_dominated_convergence hsum
    (inverseSpectralTerm_tendsto m hm hfixed) hbound
  simpa only [tsum_inverseSpectralTerm_eq_trace m _ hm, tsum_mul_left] using hlim

#print axioms inverseSpectralTerm_nonneg
#print axioms tsum_inverseSpectralTerm_eq_trace
#print axioms inverseSpectralTerm_tendsto
#print axioms toeplitz_inverse_trace_tendsto_series_of_limits_and_majorant

end MF21Restart
