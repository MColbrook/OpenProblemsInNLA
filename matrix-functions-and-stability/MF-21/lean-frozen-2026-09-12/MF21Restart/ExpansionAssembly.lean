import MF21Restart.ExpansionScalar

/-! Fixed-data assembly of the global and bulk expansion estimates.
Only the global result has the explicit finite-prefix spectral premise.
See EXPANSION_ASSEMBLY_STATEMENTS.md. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

/-- The order-p estimate for all original indices, conditional only on
the displayed low-index eigenvalue bound in addition to Taylor/tail data. -/
theorem uniformBound_of_taylor_vanishing_spectral_tail
    (m p : ℕ) (hm : 1 ≤ m) (hp : p ≤ 2 * m - 1)
    (Y : ℝ × ℝ → ℝ) (d : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hTaylor : ∀ p : ℕ, ∃ Cp : ℝ, 0 < Cp ∧
      ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, ∀ h : ℝ, |h| ≤ δ →
        |symbol m (Y (x, h)) - ∑ k ∈ Finset.range (p + 1), d k x * h ^ k| ≤
          Cp * |h| ^ (p + 1))
    (hvan : ∀ k : ℕ, k ≤ 2 * m → ∃ Ck : ℝ, 0 < Ck ∧
      ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, |d k x| ≤ Ck * x ^ (2 * m - k))
    (N J : ℕ) (Cs c : ℝ) (hCs : 0 < Cs) (hc : 0 < c)
    (hTail : ∀ n : ℕ, N ≤ n → ∀ j : ℕ, J ≤ j → j ≤ n →
      |eigenvalue m n j - symbol m (Y (mesh n j, 1 / (n + 2 : ℝ)))| ≤
        Cs * (1 / (n + 2 : ℝ)) ^ (2 * m) * (j : ℝ) ^ (2 * m - 1) *
          Real.exp (-c * (j : ℝ)))
    (hLow : ∀ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → j < J → j ≤ n →
        |eigenvalue m n j| ≤ C * (1 / (n + 2 : ℝ)) ^ (2 * m)) :
    UniformBound m d p := by
  obtain ⟨Cp, hCp, ht⟩ := hTaylor p
  obtain ⟨M, hM, hpoly⟩ := nat_pow_exp_uniform_bound (2 * m - 1) c hc
  obtain ⟨B, hB, hprefix⟩ := expansion_fixed_prefix_bound m p J (by omega) d hvan
  obtain ⟨CL, hCL, NL, hl⟩ := hLow J
  obtain ⟨Nδ, hnδ⟩ := eventually_step_le δ hδ
  let C : ℝ := CL + B + Cs * M + Cp
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, max N (max Nδ NL), hC, ?_⟩
  intro n j hn hj hjn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnδ' : Nδ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnL : NL ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  let h : ℝ := 1 / (n + 2 : ℝ)
  have hh : 0 < h := (step_pos_le_one n).1
  have hh1 : h ≤ 1 := (step_pos_le_one n).2
  have hhδ : |h| ≤ δ := by rw [abs_of_pos hh]; exact hnδ n hnδ'
  have hpow : h ^ (2 * m) ≤ h ^ (p + 1) :=
    pow_le_pow_of_le_one hh.le hh1 (by omega)
  have herr : |remainder m d p n j| ≤ C * h ^ (p + 1) := by
    by_cases hjlow : j < J
    · have he := hl n hnL j hj hjlow hjn
      have hexp := hprefix n j hjlow.le hjn
      change |eigenvalue m n j| ≤ CL * h ^ (2 * m) at he
      change |expansion d p n j| ≤ B * h ^ (2 * m) at hexp
      calc
        |remainder m d p n j| ≤ |eigenvalue m n j| + |expansion d p n j| := by
          simpa only [remainder, sub_zero, zero_sub, abs_neg] using
            (abs_sub_le (eigenvalue m n j) 0 (expansion d p n j))
        _ ≤ CL * h ^ (2 * m) + B * h ^ (2 * m) := add_le_add he hexp
        _ = (CL + B) * h ^ (2 * m) := by ring
        _ ≤ (CL + B) * h ^ (p + 1) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
        _ ≤ C * h ^ (p + 1) := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hh.le _)
          dsimp only [C]
          have : 0 < Cs * M := mul_pos hCs hM
          linarith
    · have hjtail : J ≤ j := Nat.le_of_not_gt hjlow
      have hs := hTail n hnN j hjtail hjn
      have hspec : |eigenvalue m n j - symbol m (Y (mesh n j, h))| ≤
          (Cs * M) * h ^ (p + 1) := by
        calc
          _ ≤ Cs * h ^ (2 * m) * (j : ℝ) ^ (2 * m - 1) *
              Real.exp (-c * (j : ℝ)) := hs
          _ = (Cs * h ^ (2 * m)) *
              ((j : ℝ) ^ (2 * m - 1) * Real.exp (-c * (j : ℝ))) := by ring
          _ ≤ (Cs * h ^ (2 * m)) * M :=
            mul_le_mul_of_nonneg_left (hpoly j) (by positivity)
          _ = (Cs * M) * h ^ (2 * m) := by ring
          _ ≤ (Cs * M) * h ^ (p + 1) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
      have htaylor := ht (mesh n j) (mesh_mem_interval n j hjn) h hhδ
      rw [abs_of_pos hh] at htaylor
      rw [← expansion_eq_sum_step d p n j] at htaylor
      calc
        |remainder m d p n j| ≤
            |eigenvalue m n j - symbol m (Y (mesh n j, h))| +
              |symbol m (Y (mesh n j, h)) - expansion d p n j| :=
          abs_sub_le _ _ _
        _ ≤ (Cs * M) * h ^ (p + 1) + Cp * h ^ (p + 1) :=
          add_le_add hspec htaylor
        _ = (Cs * M + Cp) * h ^ (p + 1) := by ring
        _ ≤ C * h ^ (p + 1) := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hh.le _)
          dsimp only [C]
          linarith
  simpa only [h, div_eq_mul_inv, one_mul, inv_pow] using herr

/-- The original logarithmic-squared bulk estimate requires no low-index
eigenvalue bound. Its coefficient family is exactly the fixed input d. -/
theorem bulkBound_of_taylor_spectral_tail
    (m : ℕ) (Y : ℝ × ℝ → ℝ) (d : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hTaylor : ∀ p : ℕ, ∃ Cp : ℝ, 0 < Cp ∧
      ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, ∀ h : ℝ, |h| ≤ δ →
        |symbol m (Y (x, h)) - ∑ k ∈ Finset.range (p + 1), d k x * h ^ k| ≤
          Cp * |h| ^ (p + 1))
    (N J : ℕ) (Cs c : ℝ) (hCs : 0 < Cs) (hc : 0 < c)
    (hTail : ∀ n : ℕ, N ≤ n → ∀ j : ℕ, J ≤ j → j ≤ n →
      |eigenvalue m n j - symbol m (Y (mesh n j, 1 / (n + 2 : ℝ)))| ≤
        Cs * (1 / (n + 2 : ℝ)) ^ (2 * m) * (j : ℝ) ^ (2 * m - 1) *
          Real.exp (-c * (j : ℝ))) :
    BulkBound m d := by
  obtain ⟨Cp, hCp, ht⟩ := hTaylor (2 * m)
  obtain ⟨Nδ, hnδ⟩ := eventually_step_le δ hδ
  obtain ⟨NJ, hnJ⟩ := eventually_bulk_cutoff_ge J
  obtain ⟨Nb, hgain⟩ := exists_log_sq_bulk_scale_gain c hc (2 * m - 1)
  refine ⟨Cs + Cp, max N (max Nδ (max NJ Nb)), by positivity, ?_⟩
  intro n j hn _hj hbulk hjn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnδ' : Nδ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnJN : max NJ Nb ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hnJ' : NJ ≤ n := (le_max_left _ _).trans hnJN
  have hnb : Nb ≤ n := (le_max_right _ _).trans hnJN
  have hjtail : J ≤ j := (hnJ n hnJ').trans hbulk
  let h : ℝ := 1 / (n + 2 : ℝ)
  have hh : 0 < h := (step_pos_le_one n).1
  have hden : 0 < (n + 2 : ℝ) := by positivity
  have hhδ : |h| ≤ δ := by rw [abs_of_pos hh]; exact hnδ n hnδ'
  have hsmall : (j : ℝ) ^ (2 * m - 1) * Real.exp (-c * (j : ℝ)) ≤ h := by
    apply (le_div_iff₀ hden).mpr
    have hg := hgain n hnb j hbulk
    nlinarith only [hg]
  have hspec : |eigenvalue m n j - symbol m (Y (mesh n j, h))| ≤
      Cs * h ^ (2 * m + 1) := by
    calc
      _ ≤ Cs * h ^ (2 * m) * (j : ℝ) ^ (2 * m - 1) *
          Real.exp (-c * (j : ℝ)) := hTail n hnN j hjtail hjn
      _ = (Cs * h ^ (2 * m)) *
          ((j : ℝ) ^ (2 * m - 1) * Real.exp (-c * (j : ℝ))) := by ring
      _ ≤ (Cs * h ^ (2 * m)) * h :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = Cs * h ^ (2 * m + 1) := by rw [pow_succ]; ring
  have htaylor := ht (mesh n j) (mesh_mem_interval n j hjn) h hhδ
  rw [abs_of_pos hh] at htaylor
  rw [← expansion_eq_sum_step d (2 * m) n j] at htaylor
  have herr : |remainder m d (2 * m) n j| ≤ (Cs + Cp) * h ^ (2 * m + 1) := by
    calc
      _ ≤ |eigenvalue m n j - symbol m (Y (mesh n j, h))| +
          |symbol m (Y (mesh n j, h)) - expansion d (2 * m) n j| :=
        abs_sub_le _ _ _
      _ ≤ Cs * h ^ (2 * m + 1) + Cp * h ^ (2 * m + 1) :=
        add_le_add hspec htaylor
      _ = _ := by ring
  simpa only [h, div_eq_mul_inv, one_mul, inv_pow] using herr

#print axioms uniformBound_of_taylor_vanishing_spectral_tail
#print axioms bulkBound_of_taylor_spectral_tail

end MF21Restart
