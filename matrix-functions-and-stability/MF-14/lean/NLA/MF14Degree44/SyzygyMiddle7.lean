/- An exact symbolic middle-coefficient cancellation from Marcus Webb's syzygy.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; substantial Codex assistance. -/
import NLA.MF14Degree44.DegenerationCoefficientData
import Mathlib.Tactic.Ring
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.MF14Degree44

theorem syzygy_middle7_zero (alpha eta gamma s : ℂ) :
    syzygyMiddle7For alpha eta gamma s (syzygyCoefficients alpha eta gamma s) = 0 := by
  dsimp [syzygyMiddle7For, syzygyCoefficients, syzygyR5, syzygyR6,
    syzygyCoefficient1, syzygyCoefficient2, syzygyCoefficient3,
    syzygyCoefficient4, syzygyCoefficient5]
  ring

#print axioms syzygy_middle7_zero
#assert_trust kernel syzygy_middle7_zero
end NLA.MF14Degree44
