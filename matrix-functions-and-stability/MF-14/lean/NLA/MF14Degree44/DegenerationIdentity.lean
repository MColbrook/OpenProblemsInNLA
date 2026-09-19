/- Complete exact syzygy identity for the degree44 border construction.
Mathematical certificate: Marcus Webb, The University of Manchester.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; substantial Codex assistance. -/
import NLA.MF14Degree44.SyzygyExpansion
import NLA.MF14Degree44.SyzygyFactors
import NLA.MF14Degree44.SyzygyMiddle7
import NLA.MF14Degree44.SyzygyMiddle8
import NLA.MF14Degree44.SyzygyMiddle9
import NLA.MF14Degree44.SyzygyMiddle10
import NLA.MF14Degree44.SyzygyLowPart
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
open scoped BigOperators
namespace NLA.MF14Degree44

theorem degeneration_high_part (alpha eta gamma s : ℂ) :
    syzygyHighPartFor alpha eta gamma s (syzygyCoefficients alpha eta gamma s) =
      -(C (s ^ 4) * degenerationZ alpha eta gamma s) := by
  simp [syzygyHighPartFor, syzygy_third_factor, syzygy_fourth_factor,
    syzygyR5, syzygyR6, degenerationZ,
    map_add, map_mul, map_pow, map_ofNat, map_neg, map_sub] <;> ring

theorem degeneration_decomposition (alpha eta gamma s : ℂ) :
    degenerationE alpha eta gamma s =
      syzygyLowPartFor alpha eta gamma s (syzygyCoefficients alpha eta gamma s) -
      C (s ^ 4) * degenerationZ alpha eta gamma s := by
  unfold degenerationE
  rw [syzygy_polynomial_expansion, syzygy_middle7_zero, syzygy_middle8_zero,
    syzygy_middle9_zero, syzygy_middle10_zero]
  simp only [map_zero, zero_mul, add_zero, degeneration_high_part, sub_eq_add_neg]

theorem degeneration_low_part (alpha eta gamma s : ℂ) :
    lowPart6 (degenerationE alpha eta gamma s) =
      syzygyLowPartFor alpha eta gamma s (syzygyCoefficients alpha eta gamma s) := by
  ext n
  rw [lowPart6_coeff]
  by_cases hn : n < 7
  · rw [if_pos hn, degeneration_decomposition, coeff_sub,
      scaled_degenerationZ_low_coeff alpha eta gamma s n hn, sub_zero]
  · rw [if_neg hn,
      syzygy_low_part_high_coeff alpha eta gamma s _ n (Nat.le_of_not_gt hn)]

/-- Every complex parameter, including s=0, satisfies the entire polynomial identity. -/
theorem degeneration_identity (alpha eta gamma s : ℂ) :
    degenerationE alpha eta gamma s - lowPart6 (degenerationE alpha eta gamma s) =
      -(C (s ^ 4) * degenerationZ alpha eta gamma s) := by
  rw [degeneration_low_part, degeneration_decomposition]
  abel

#print axioms degeneration_high_part
#assert_trust kernel degeneration_high_part
#print axioms degeneration_decomposition
#assert_trust kernel degeneration_decomposition
#print axioms degeneration_low_part
#assert_trust kernel degeneration_low_part
#print axioms degeneration_identity
#assert_trust kernel degeneration_identity
end NLA.MF14Degree44
