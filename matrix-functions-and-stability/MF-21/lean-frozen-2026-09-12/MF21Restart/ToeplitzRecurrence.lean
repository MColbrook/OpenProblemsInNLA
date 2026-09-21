import MF21Restart.FourierStencil
import MF21Restart.FiniteRecurrence

/-! The actual Fourier-defined matrix equals the finite convolution with
the manuscript's zero ghost entries, including the Fourier sign convention. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix

namespace MF21Restart

theorem zeroGhost_convolution_eq_toeplitz_mulVec
    (m n : ℕ) (v : Fin n → ℂ) (k : Fin n) :
    (∑ t : Fin (2 * m + 1),
      (fourierCoeff m ((t.val : ℤ) - (m : ℤ)) : ℂ) *
        zeroGhostExtension m n v (k.val + t.val)) =
      ((toeplitz m n).map Complex.ofReal *ᵥ v) k := by
  classical
  let f : Fin (2 * m + 1) → ℂ := fun t =>
    (fourierCoeff m ((t.val : ℤ) - (m : ℤ)) : ℂ) *
      zeroGhostExtension m n v (k.val + t.val)
  let g : Fin n → ℂ := fun j =>
    (fourierCoeff m ((k.val : ℤ) - (j.val : ℤ)) : ℂ) * v j
  change (∑ t, f t) = ∑ j, g j
  have hactive : ∀ t, f t ≠ 0 → m ≤ k.val + t.val ∧ k.val + t.val < m + n := by
    intro t ht
    by_contra h
    exact ht (by simp [f, zeroGhostExtension, h])
  have hterm : ∀ (t : Fin (2 * m + 1)) (j : Fin n),
      k.val + t.val = m + j.val → f t = g j := by
    intro t j heq
    have hidx : (t.val : ℤ) - (m : ℤ) = -((k.val : ℤ) - (j.val : ℤ)) := by omega
    dsimp only [f, g]
    rw [heq, zeroGhostExtension_middle, hidx, fourierCoeff_neg]
  let idx : ∀ t, f t ≠ 0 → Fin n := fun t ht =>
    ⟨k.val + t.val - m, by have h := hactive t ht; omega⟩
  apply Finset.sum_bij_ne_zero (fun t _ ht => idx t ht)
  · intro t _ ht
    exact Finset.mem_univ _
  · intro a _ ha b _ hb hab
    apply Fin.ext
    have hv := congrArg Fin.val hab
    have hma := hactive a ha
    have hmb := hactive b hb
    dsimp [idx] at hv
    omega
  · intro j _ hj
    have hc : fourierCoeff m ((k.val : ℤ) - (j.val : ℤ)) ≠ 0 := by
      intro hc
      exact hj (by simp [g, hc])
    have habs : |(k.val : ℤ) - (j.val : ℤ)| ≤ (m : ℤ) := by
      by_contra h
      exact hc (fourierCoeff_support m _ (by omega))
    have hbounds := abs_le.mp habs
    let t : Fin (2 * m + 1) := ⟨m + j.val - k.val, by omega⟩
    have heq : k.val + t.val = m + j.val := by dsimp [t]; omega
    have hfg := hterm t j heq
    have ht : f t ≠ 0 := by simpa only [hfg] using hj
    refine ⟨t, Finset.mem_univ _, ht, ?_⟩
    apply Fin.ext
    dsimp [idx]
    omega
  · intro t _ ht
    apply hterm t (idx t ht)
    have h := hactive t ht
    dsimp [idx]
    omega

#print axioms zeroGhost_convolution_eq_toeplitz_mulVec

end MF21Restart
