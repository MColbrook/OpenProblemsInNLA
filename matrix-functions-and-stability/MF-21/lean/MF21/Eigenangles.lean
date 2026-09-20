import MF21.SpectralBounds
import MF21.BulkSymbol
import Mathlib.Topology.Order.IntermediateValue

/-! The actual ordered eigenangles, defined using the exact symbol and the
strict spectral endpoint bounds. -/

open Set
noncomputable section
namespace MF21Challenge

theorem symbol_strictMonoOn (m : ℕ) (hm : 0 < m) :
    StrictMonoOn (symbol m) (Icc 0 Real.pi) := by
  intro x hx y hy hxy
  rcases hx with ⟨hx0, hxpi⟩
  rcases hy with ⟨hy0, hypi⟩
  have hs : Real.sin (x/2) < Real.sin (y/2) :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (by linarith [Real.pi_pos]) (by linarith) (by linarith)
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0 ≤ x/2 by linarith) (show x/2 ≤ Real.pi by linarith [Real.pi_pos])
  exact pow_lt_pow_left₀ (by linarith) (by positivity) (by omega : 2*m ≠ 0)

@[simp] theorem symbol_zero (m : ℕ) (hm : 0 < m) : symbol m 0 = 0 := by
  simp [symbol, show 2*m ≠ 0 by omega]

@[simp] theorem symbol_pi (m : ℕ) : symbol m Real.pi = (4 : ℝ)^m := by
  simp only [symbol, Real.sin_pi_div_two, mul_one, pow_mul]
  norm_num

theorem eigenvalue_monotone (m n : ℕ) : Monotone (eigenvalue m n) := by
  intro i j hij
  exact (toeplitz_isHermitian m n).eigenvalues₀_antitone (Fin.rev_le_rev.mpr hij)

theorem exists_unique_eigenangle (m n : ℕ) (hm : 0 < m) (j : Fin n) :
    ∃! t : ℝ, t ∈ Ioo 0 Real.pi ∧ symbol m t = eigenvalue m n j := by
  have hp := eigenvalue_pos m n j
  have hu := MF21Circulant.toeplitz_eigenvalue_strict_upper m n hm j
  have hmem : eigenvalue m n j ∈ Icc (symbol m 0) (symbol m Real.pi) := by
    rw [symbol_zero m hm, symbol_pi]
    exact ⟨le_of_lt hp, le_of_lt hu⟩
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc (le_of_lt Real.pi_pos)
    (symbol_contDiff m).continuous.continuousOn hmem
  have ht0 : 0 < t := by
    apply lt_of_le_of_ne ht.1
    intro h
    rw [← h, symbol_zero m hm] at he
    linarith
  have htpi : t < Real.pi := by
    apply lt_of_le_of_ne ht.2
    intro h
    rw [h, symbol_pi] at he
    linarith
  refine ⟨t, ⟨⟨ht0, htpi⟩, he⟩, ?_⟩
  intro s hs
  exact (symbol_strictMonoOn m hm).injOn ⟨le_of_lt hs.1.1, le_of_lt hs.1.2⟩ ht
    (hs.2.trans he.symm)

def eigenangle (m n : ℕ) (hm : 0 < m) (j : Fin n) : ℝ :=
  (exists_unique_eigenangle m n hm j).exists.choose

theorem eigenangle_mem (m n : ℕ) (hm : 0 < m) (j : Fin n) :
    eigenangle m n hm j ∈ Ioo 0 Real.pi :=
  (exists_unique_eigenangle m n hm j).exists.choose_spec.1

@[simp] theorem symbol_eigenangle (m n : ℕ) (hm : 0 < m) (j : Fin n) :
    symbol m (eigenangle m n hm j) = eigenvalue m n j :=
  (exists_unique_eigenangle m n hm j).exists.choose_spec.2

theorem eigenangle_monotone (m n : ℕ) (hm : 0 < m) : Monotone (eigenangle m n hm) := by
  intro i j hij
  have hi := eigenangle_mem m n hm i
  have hj := eigenangle_mem m n hm j
  apply (symbol_strictMonoOn m hm).le_iff_le ⟨le_of_lt hi.1, le_of_lt hi.2⟩
    ⟨le_of_lt hj.1, le_of_lt hj.2⟩ |>.mp
  simpa only [symbol_eigenangle] using eigenvalue_monotone m n hij

theorem eigenangle_eq_iff (m n : ℕ) (hm : 0 < m) (j : Fin n) (t : ℝ)
    (ht : t ∈ Ioo 0 Real.pi) :
    eigenangle m n hm j = t ↔ symbol m t = eigenvalue m n j := by
  constructor
  · intro h
    rw [← h, symbol_eigenangle]
  · intro h
    exact (exists_unique_eigenangle m n hm j).unique
      ⟨eigenangle_mem m n hm j, symbol_eigenangle m n hm j⟩ ⟨ht, h⟩

end MF21Challenge

#print axioms MF21Challenge.exists_unique_eigenangle
#print axioms MF21Challenge.eigenangle_monotone
#print axioms MF21Challenge.eigenangle_eq_iff
