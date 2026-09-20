import MF21.PhaseErrorEstimate

open Set
open scoped Topology
noncomputable section
namespace MF21Phase

/-- A uniform natural-number cutoff for a decaying exponential. -/
theorem exists_exp_cutoff (A a eps : ℝ) (hA : 0 ≤ A) (ha : 0 < a)
    (heps : 0 < eps) : ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      A * Real.exp (-a*n) ≤ eps := by
  by_cases hAz : A = 0
  · exact ⟨1, le_refl _, by simpa [hAz] using (fun (_ : ℕ) (_ : 1 ≤ _) ↦ le_of_lt heps)⟩
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (Real.log (A/eps)/a))
  refine ⟨N, ?_, ?_⟩
  · have : (1 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN
    exact_mod_cast (le_of_lt this)
  intro n hn
  have hna : Real.log (A/eps) ≤ a*n := by
    have hnr : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : Real.log (A/eps)/a ≤ (n : ℝ) :=
      (le_max_right _ _).trans (le_of_lt hN |>.trans hnr)
    exact (div_le_iff₀ ha).mp hlog |>.trans_eq (mul_comm _ _)
  have hex : Real.exp (-a*n) ≤ (A/eps)⁻¹ := by
    rw [← Real.exp_log (div_pos hAp heps), ← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    A*Real.exp (-a*n) ≤ A*(A/eps)⁻¹ := mul_le_mul_of_nonneg_left hex hA
    _ = eps := by field_simp

/-- A lower bound in the entire phase tail, without a cell upper bound. -/
theorem phase_tail_angle_lower (eta : ℝ → ℝ) (M : ℝ) (n J : ℕ)
    (hn : 1 ≤ n) (theta : ℝ) (htheta : 0 ≤ theta)
    (heta : |eta theta| ≤ M)
    (htail : J*Real.pi-Real.pi/4 ≤ phase n eta theta) :
    ((J : ℝ)*Real.pi-Real.pi/4-M)/3 ≤ (n : ℝ)*theta := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he := (abs_le.mp heta).1
  have hnon := mul_nonneg (show 0 ≤ (n : ℝ)-1 by linarith) htheta
  dsimp only [phase] at htail
  nlinarith

/-- The constant-index tail makes both remainder bounds small uniformly in n. -/
theorem exists_small_phase_tail (eta : ℝ → ℝ) (M C c : ℝ)
    (_hM : 0 ≤ M) (hC : 0 ≤ C) (hc : 0 < c)
    (heta : ∀ t ∈ Icc 0 Real.pi, |eta t| ≤ M) :
    ∃ J : ℕ, 1 ≤ J ∧ phase 0 eta 0 < J*Real.pi-Real.pi/4 ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ t ∈ Icc 0 Real.pi,
      J*Real.pi-Real.pi/4 ≤ phase n eta t →
      C*Real.exp (-c*n*t) ≤ (1 : ℝ)/8 := by
  obtain ⟨J₀, hJ₀, hcut⟩ := exists_exp_cutoff
    (C*Real.exp (c*(Real.pi/4+M)/3)) (c*Real.pi/3) (1/8)
    (by positivity) (by positivity) (by norm_num)
  obtain ⟨J₁, hJ₁⟩ := exists_nat_gt ((M+Real.pi/4)/Real.pi)
  let J := max J₀ J₁
  have hJJ₀ : J₀ ≤ J := le_max_left _ _
  have hJJ₁ : J₁ ≤ J := le_max_right _ _
  have hJphase : M < (J : ℝ)*Real.pi-Real.pi/4 := by
    have hh : (J₁ : ℝ) ≤ J := by exact_mod_cast hJJ₁
    have hmul := (div_lt_iff₀ Real.pi_pos).mp (hJ₁.trans_le hh)
    linarith
  refine ⟨J, hJ₀.trans hJJ₀, ?_, ?_⟩
  · have hη := (abs_le.mp (heta 0 ⟨le_refl _, le_of_lt Real.pi_pos⟩)).1
    dsimp [phase]
    linarith
  intro n hn t ht htail
  have hb := phase_tail_angle_lower eta M n J hn t ht.1 (heta t ht) htail
  have he : Real.exp (-c*n*t) ≤
      Real.exp (c*(Real.pi/4+M)/3)*Real.exp (-(c*Real.pi/3)*J) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    C*Real.exp (-c*n*t) ≤ C*(Real.exp (c*(Real.pi/4+M)/3)*
        Real.exp (-(c*Real.pi/3)*J)) := mul_le_mul_of_nonneg_left he hC
    _ = (C*Real.exp (c*(Real.pi/4+M)/3))*Real.exp (-(c*Real.pi/3)*J) := by ring
    _ ≤ 1/8 := hcut J hJJ₀

/-- Derivative and final-cell estimates hold uniformly for sufficiently large matrices. -/
theorem exists_final_phase_cutoff (eta deta : ℝ → ℝ) (M K C c : ℝ)
    (hC : 0 ≤ C) (hc : 0 < c)
    (heta : ∀ t ∈ Icc 0 Real.pi, |eta t| ≤ M)
    (hder : ∀ t ∈ Icc 0 Real.pi, HasDerivAt eta (deta t) t)
    (hdeta : ∀ t ∈ Icc 0 Real.pi, |deta t| ≤ K)
    (hetapi : eta Real.pi = Real.pi) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (∀ t ∈ Icc 0 Real.pi,
        HasDerivAt (phase n eta) ((n : ℝ)+2-deta t) t ∧
        ((n : ℝ)+2)/2 ≤ (n : ℝ)+2-deta t) ∧
      phase n eta Real.pi = (n+1)*Real.pi ∧
      ∀ (E : ℝ → ℝ)
        (_hE : ∀ t ∈ Ioo 0 Real.pi, Real.pi/2 ≤ t →
          |E t| ≤ C*n*Real.exp (-(c*Real.pi/2)*n)*(Real.pi-t))
        (t : ℝ), t ∈ Ioo 0 Real.pi →
        |phase n eta t-(n+1)*Real.pi| ≤ Real.pi/4 →
        Real.sin (phase n eta t)+E t ≠ 0 := by
  obtain ⟨N₀, hN₀, hcut⟩ := exists_exp_cutoff (Real.pi*C) (c*Real.pi/2) (1/2)
    (by positivity) (by positivity) (by norm_num)
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (max (2*K) (2*(Real.pi/4+M)/Real.pi))
  let N := max N₀ N₁
  have hNN₀ : N₀ ≤ N := le_max_left _ _
  have hNN₁ : N₁ ≤ N := le_max_right _ _
  refine ⟨N, hN₀.trans hNN₀, ?_⟩
  intro n hn
  have hN₁n : (N₁ : ℝ) ≤ n := by exact_mod_cast hNN₁.trans hn
  have hKn : 2*K ≤ (n : ℝ) := (le_max_left _ _).trans (le_of_lt hN₁ |>.trans hN₁n)
  have hMn : Real.pi/4+M ≤ (n : ℝ)*Real.pi/2 := by
    have hh : 2*(Real.pi/4+M)/Real.pi ≤ (n : ℝ) :=
      (le_max_right _ _).trans (le_of_lt hN₁ |>.trans hN₁n)
    have hmul := (div_le_iff₀ Real.pi_pos).mp hh
    linarith
  have hphaseDer (t : ℝ) (ht : t ∈ Icc 0 Real.pi) :
      HasDerivAt (phase n eta) ((n : ℝ)+2-deta t) t := by
    rw [show phase n eta = (fun x : ℝ ↦ ((n : ℝ)+2)*x)-eta from rfl]
    apply HasDerivAt.sub
    · have hh : HasDerivAt (fun x : ℝ ↦ ((n : ℝ)+2)*x) (((n : ℝ)+2)*1) t :=
        (hasDerivAt_id t).const_mul ((n : ℝ)+2)
      simpa only [mul_one] using hh
    · exact hder t ht
  have hlower (t : ℝ) (ht : t ∈ Icc 0 Real.pi) :
      ((n : ℝ)+2)/2 ≤ (n : ℝ)+2-deta t := by
    have hh := (abs_le.mp (hdeta t ht)).2
    linarith
  have hpi : phase n eta Real.pi = (n+1)*Real.pi := by dsimp [phase]; rw [hetapi]; ring
  refine ⟨fun t ht ↦ ⟨hphaseDer t ht, hlower t ht⟩, hpi, ?_⟩
  intro E hE t ht hcell
  have htc : t ∈ Icc 0 Real.pi := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have htlo : Real.pi/2 ≤ t := by
    have he := (abs_le.mp (heta t htc)).1
    have hf := (abs_le.mp hcell).1
    dsimp only [phase] at hf
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith [Real.pi_pos]
  have hErr : |E t| ≤ (C*n*Real.exp (-(c*Real.pi/2)*n))*(Real.pi-t) := hE t ht htlo
  have hcErr : Real.pi/2*(C*n*Real.exp (-(c*Real.pi/2)*n)) < ((n : ℝ)+2)/2 := by
    have hh := hcut n (hNN₀.trans hn)
    have hh' := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg n)
    nlinarith
  apply final_cell_no_root (phase n eta) (fun t ↦ (n : ℝ)+2-deta t)
    0 Real.pi (((n : ℝ)+2)/2) (C*n*Real.exp (-(c*Real.pi/2)*n)) (E t) t (n+1)
    (by positivity) hphaseDer hlower ⟨le_of_lt ht.1, ht.2⟩
    (by simpa only [Nat.cast_add, Nat.cast_one] using hpi)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hcell.trans (by linarith [Real.pi_pos]))
    hErr hcErr

/-- The fixed-index cutoff and matrix-size cutoff in the perturbed-sine
quantization argument follow from the actual exponential estimates. -/
theorem eventual_indexed_phase_roots
    (eta deta : ℝ → ℝ) (E dE : ℕ → ℝ → ℝ)
    (M K C c : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C) (hc : 0 < c)
    (heta : ∀ t ∈ Icc 0 Real.pi, |eta t| ≤ M)
    (hder : ∀ t ∈ Icc 0 Real.pi, HasDerivAt eta (deta t) t)
    (hdeta : ∀ t ∈ Icc 0 Real.pi, |deta t| ≤ K)
    (hetapi : eta Real.pi = Real.pi) (n₀ : ℕ)
    (theta : ∀ n : ℕ, Fin n → ℝ)
    (htheta : ∀ n, Monotone (theta n))
    (htheta_mem : ∀ n j, theta n j ∈ Ioo 0 Real.pi)
    (hEder : ∀ n, n₀ ≤ n → ∀ t ∈ Ioo 0 Real.pi, HasDerivAt (E n) (dE n t) t)
    (hEbd : ∀ n, n₀ ≤ n → ∀ t ∈ Ioo 0 Real.pi,
      |E n t| ≤ C*Real.exp (-c*n*t) ∧ |dE n t| ≤ C*n*Real.exp (-c*n*t))
    (hEndpoint : ∀ n, n₀ ≤ n → ∀ t ∈ Ioo 0 Real.pi, Real.pi/2 ≤ t →
      |E n t| ≤ C*n*Real.exp (-(c*Real.pi/2)*n)*(Real.pi-t))
    (hspectrum : ∀ n, n₀ ≤ n → ∀ t ∈ Ioo 0 Real.pi,
      Real.sin (phase n eta t)+E n t = 0 ↔ ∃ i : Fin n, theta n i = t)
    (hsimple : ∀ n, n₀ ≤ n → ∀ t ∈ Ioo 0 Real.pi,
      Real.sin (phase n eta t)+E n t = 0 →
      deriv (fun x ↦ Real.sin (phase n eta x)+E n x) t ≠ 0 →
      ∀ i k : Fin n, theta n i = t → theta n k = t → i = k) :
    ∃ J N : ℕ, 1 ≤ J ∧ 1 ≤ N ∧ n₀ ≤ N ∧ ∀ n, N ≤ n →
      ∀ j : Fin n, J ≤ j.val+1 →
      |phase n eta (theta n j)-(j.val+1)*Real.pi| ≤ Real.pi/4 ∧
      deriv (fun t ↦ Real.sin (phase n eta t)+E n t) (theta n j) ≠ 0 ∧
      |phase n eta (theta n j)-(j.val+1)*Real.pi| ≤ (Real.pi/2)*|E n (theta n j)| := by
  obtain ⟨J, hJ, hJ0, htail⟩ := exists_small_phase_tail eta M C c hM hC hc heta
  obtain ⟨N₁, hN₁, hNspec⟩ := exists_final_phase_cutoff eta deta M K C c hC hc
    heta hder hdeta hetapi
  let N := max n₀ N₁
  refine ⟨J, N, hJ, hN₁.trans (le_max_right _ _), le_max_left _ _, ?_⟩
  intro n hn
  have hn₀ : n₀ ≤ n := (le_max_left _ _).trans hn
  have hn₁ : N₁ ≤ n := (le_max_right _ _).trans hn
  have hnpos : 1 ≤ n := hN₁.trans hn₁
  obtain ⟨hD, hpi, hfinal⟩ := hNspec n hn₁
  apply indexed_phase_roots (phase n eta) (E n) (fun t ↦ (n : ℝ)+2-deta t)
    (dE n) (((n : ℝ)+2)/2) (by positivity) J n hJ (theta n)
    (htheta n) (htheta_mem n) (fun t ht ↦ (hD t ht).1) (hEder n hn₀)
    (fun t ht ↦ (hD t ht).2)
  · simpa only [phase, mul_zero, Nat.cast_zero] using hJ0
  · exact hpi
  · intro t ht hphase
    have hsmall := htail n hnpos t ⟨le_of_lt ht.1, le_of_lt ht.2⟩ hphase
    have hb := hEbd n hn₀ t ht
    constructor
    · exact hb.1.trans (hsmall.trans (by norm_num))
    · have hmul := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg n)
      nlinarith [hb.2]
  · exact hspectrum n hn₀
  · exact hsimple n hn₀
  · exact hfinal (E n) (hEndpoint n hn₀)

end MF21Phase

#print axioms MF21Phase.exists_exp_cutoff
#print axioms MF21Phase.exists_small_phase_tail
#print axioms MF21Phase.exists_final_phase_cutoff
#print axioms MF21Phase.eventual_indexed_phase_roots
