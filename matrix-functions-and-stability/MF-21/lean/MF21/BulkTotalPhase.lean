import MF21.BulkPhase

noncomputable section
open Filter
open scoped Topology ContDiff BigOperators
namespace MF21Bulk

def nontrivialIndex (m : ℕ) (j : Fin (m - 1)) : Fin m := ⟨j.val + 1, by omega⟩

theorem nontrivialIndex_ne_zero (m : ℕ) (j : Fin (m - 1)) :
    (nontrivialIndex m j).val ≠ 0 := by simp [nontrivialIndex]

def psi (m : ℕ) (theta : ℝ) : ℝ :=
  ∑ j : Fin (m - 1), rootPhase (omega m (nontrivialIndex m j)) theta

theorem omega_nontrivial_rev (m : ℕ) (hm : 0 < m) (j : Fin (m - 1)) :
    omega m (nontrivialIndex m j.rev) =
      (starRingEnd ℂ) (omega m (nontrivialIndex m j)) := by
  rw [← Complex.inv_eq_conj (omega_norm m (nontrivialIndex m j))]
  have he : (nontrivialIndex m j.rev).val + (nontrivialIndex m j).val = m := by
    simp only [nontrivialIndex, Fin.val_rev]
    omega
  apply eq_inv_of_mul_eq_one_left
  rw [omega, omega, ← pow_add, he,
    (Complex.isPrimitiveRoot_exp m (ne_of_gt hm)).pow_eq_one]

theorem psi_pi (m : ℕ) (hm : 0 < m) : psi m Real.pi = 0 := by
  have hrev : (∑ j : Fin (m - 1),
      rootPhase (omega m (nontrivialIndex m j.rev)) Real.pi) = psi m Real.pi := by
    exact Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (m - 1)))
      (fun j => rootPhase (omega m (nontrivialIndex m j)) Real.pi)
  have hneg : (∑ j : Fin (m - 1),
      rootPhase (omega m (nontrivialIndex m j.rev)) Real.pi) = -psi m Real.pi := by
    unfold psi
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [omega_nontrivial_rev m hm j]
    exact rootPhase_conj_pi _ (omega_norm m (nontrivialIndex m j))
      (omega_ne_one m hm _ (nontrivialIndex_ne_zero m j))
  linarith

theorem psi_contDiffAt (m : ℕ) (hm : 0 < m) (theta : ℝ)
    (hs : 0 < spectralBase theta) : ContDiffAt ℝ ∞ (psi m) theta := by
  unfold psi
  apply ContDiffAt.sum
  intro j _
  exact rootPhase_contDiffAt _ theta hs (omega_norm m (nontrivialIndex m j))
    (omega_ne_one m hm _ (nontrivialIndex_ne_zero m j))

theorem sum_fin_add_one (n : ℕ) :
    (∑ j : Fin n, ((j.val : ℝ) + 1)) = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    push_cast
    ring

theorem endpoint_phase_sum (m : ℕ) (hm : 0 < m) :
    (∑ j : Fin (m - 1), Complex.arg (kappa m (nontrivialIndex m j) + Complex.I)) =
      (m - 1 : ℝ) * Real.pi / 4 := by
  have hterms (j : Fin (m - 1)) :
      Complex.arg (kappa m (nontrivialIndex m j) + Complex.I) =
        Real.pi / (2 * m) * ((j.val : ℝ) + 1) := by
    rw [arg_kappa_add_I m hm _ (nontrivialIndex_ne_zero m j)]
    simp only [nontrivialIndex, Nat.cast_add, Nat.cast_one]
    ring
  simp_rw [hterms]
  rw [← Finset.mul_sum, sum_fin_add_one]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hm
  rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  field_simp
  ring

/-- A smooth local extension of the complete simple-loop phase at zero,
with the exact endpoint constant used by the trace obstruction. -/
theorem psi_endpoint_extension_analytic (m : ℕ) (hm : 0 < m) :
    ∃ P : ℝ → ℝ, P 0 = (m - 1 : ℝ) * Real.pi / 4 ∧ ContDiffAt ℝ ω P 0 ∧
      ∀ᶠ theta : ℝ in 𝓝[>] 0, P theta = psi m theta := by
  have hlocal (j : Fin (m - 1)) := rootPhase_endpoint_extension_analytic
    (omega m (nontrivialIndex m j)) (kappa m (nontrivialIndex m j))
    (omega_norm m (nontrivialIndex m j))
    (omega_ne_one m hm _ (nontrivialIndex_ne_zero m j))
    (kappa_sq m _) (kappa_re_pos m hm _ (nontrivialIndex_ne_zero m j))
  choose P hP0 hPc hPe using hlocal
  refine ⟨fun theta => ∑ j, P j theta, ?_, ?_, ?_⟩
  · simp only [hP0]
    exact endpoint_phase_sum m hm
  · exact ContDiffAt.sum fun j _ => hPc j
  · have hall : ∀ᶠ theta : ℝ in 𝓝[>] 0, ∀ j, P j theta =
        rootPhase (omega m (nontrivialIndex m j)) theta :=
      Filter.eventually_all.mpr hPe
    filter_upwards [hall] with theta he
    exact Finset.sum_congr rfl fun j _ => he j

theorem psi_endpoint_extension (m : ℕ) (hm : 0 < m) :
    ∃ P : ℝ → ℝ, P 0 = (m - 1 : ℝ) * Real.pi / 4 ∧ ContDiffAt ℝ ∞ P 0 ∧
      ∀ᶠ theta : ℝ in 𝓝[>] 0, P theta = psi m theta := by
  obtain ⟨P, h0, hc, he⟩ := psi_endpoint_extension_analytic m hm
  exact ⟨P, h0, hc.of_le (by simp), he⟩

/-- One fixed interval on which the endpoint extension is smooth to all
orders. Analytic regularity, rather than only smoothness at a point,
supplies the common interval needed by the uniform inverse theorem. -/
theorem psi_endpoint_neighborhood (m : ℕ) (hm : 0 < m) :
    ∃ P : ℝ → ℝ, ∃ delta : ℝ, 0 < delta ∧
      P 0 = (m - 1 : ℝ) * Real.pi / 4 ∧
      (∀ theta ∈ Set.Ioo (-delta) delta, ContDiffAt ℝ ∞ P theta) ∧
      (∀ theta ∈ Set.Ioo 0 delta, P theta = psi m theta) := by
  obtain ⟨P, h0, hc, he⟩ := psi_endpoint_extension_analytic m hm
  have hcs : ∀ᶠ theta : ℝ in 𝓝 0, ContDiffAt ℝ ∞ P theta :=
    (hc.eventually (by simp)).mono fun _ h => h.of_le (by simp)
  rw [eventually_nhdsWithin_iff] at he
  obtain ⟨delta, hd, hnear⟩ := Metric.eventually_nhds_iff.mp (hcs.and he)
  refine ⟨P, delta, hd, h0, ?_, ?_⟩
  · intro theta ht
    apply (hnear ?_).1
    simpa [Real.dist_eq] using abs_lt.mpr ht
  · intro theta ht
    apply (hnear ?_).2 ht.1
    simp only [Real.dist_eq, sub_zero, abs_of_pos ht.1]
    exact ht.2

end MF21Bulk

#print axioms MF21Bulk.psi_pi
#print axioms MF21Bulk.psi_contDiffAt
#print axioms MF21Bulk.psi_endpoint_extension
#print axioms MF21Bulk.psi_endpoint_neighborhood
