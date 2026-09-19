/- Exact coefficient support for lowPart6; it is never a circuit primitive.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; substantial Codex assistance. -/
import NLA.MF14Degree44.DegenerationCoefficientData
import Mathlib.Algebra.Polynomial.Coeff
import Lean.Elab.Tactic.Omega
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
open scoped BigOperators
namespace NLA.MF14Degree44

theorem lowPart6_coeff (p : Poly) (n : ℕ) :
    (lowPart6 p).coeff n = if n < 7 then p.coeff n else 0 := by
  classical
  simp only [lowPart6, finsetSum_coeff, coeff_C_mul_X_pow]
  by_cases hn : n < 7
  · rw [if_pos hn, Finset.sum_eq_single (⟨n, hn⟩ : Fin 7)]
    · simp
    · intro j _ hj
      have hnj : n ≠ j.val := by
        intro h
        apply hj
        apply Fin.ext
        exact h.symm
      simp [hnj]
    · simp
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro j _
    have hnj : n ≠ j.val := by omega
    simp [hnj]

theorem syzygy_low_part_high_coeff (alpha eta gamma s : ℂ) (c : Fin 5 → ℂ)
    (n : ℕ) (hn : 7 ≤ n) : (syzygyLowPartFor alpha eta gamma s c).coeff n = 0 := by
  have h4 : n ≠ 4 := by omega
  have h5 : n ≠ 5 := by omega
  have h6 : n ≠ 6 := by omega
  simp only [syzygyLowPartFor, coeff_add, coeff_C_mul_X_pow,
    if_neg h4, if_neg h5, if_neg h6, add_zero]

theorem scaled_degenerationZ_low_coeff (alpha eta gamma s : ℂ)
    (n : ℕ) (hn : n < 7) : (C (s ^ 4) * degenerationZ alpha eta gamma s).coeff n = 0 := by
  have h11 : n ≠ 11 := by omega
  have h12 : n ≠ 12 := by omega
  have h13 : n ≠ 13 := by omega
  have h14 : n ≠ 14 := by omega
  have h15 : n ≠ 15 := by omega
  have h16 : n ≠ 16 := by omega
  rw [coeff_C_mul]
  simp only [degenerationZ, coeff_add, coeff_C_mul_X_pow,
    if_neg h11, if_neg h12, if_neg h13, if_neg h14, if_neg h15, if_neg h16,
    add_zero, mul_zero]

#print axioms lowPart6_coeff
#assert_trust kernel lowPart6_coeff
#print axioms syzygy_low_part_high_coeff
#assert_trust kernel syzygy_low_part_high_coeff
#print axioms scaled_degenerationZ_low_coeff
#assert_trust kernel scaled_degenerationZ_low_coeff
end NLA.MF14Degree44
