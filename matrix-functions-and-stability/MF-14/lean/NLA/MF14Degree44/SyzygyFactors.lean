/- Exact scalar factors in Marcus Webb's symbolic certificate.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; substantial Codex assistance. -/
import NLA.MF14Degree44.DegenerationCoefficientData
import Mathlib.Tactic.Ring
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.MF14Degree44

theorem syzygy_third_factor (alpha eta gamma s : ℂ) :
    syzygyCoefficients alpha eta gamma s 2 = s ^ 2 * borderC alpha eta gamma s := by
  change syzygyCoefficient3 alpha eta gamma s = s ^ 2 * borderC alpha eta gamma s
  unfold syzygyCoefficient3 borderC
  ring

theorem syzygy_fourth_factor (alpha eta gamma s : ℂ) :
    syzygyCoefficients alpha eta gamma s 3 = s ^ 3 * borderD alpha eta gamma s := by
  change syzygyCoefficient4 alpha eta gamma s = s ^ 3 * borderD alpha eta gamma s
  unfold syzygyCoefficient4 borderD
  ring

#print axioms syzygy_third_factor
#assert_trust kernel syzygy_third_factor
#print axioms syzygy_fourth_factor
#assert_trust kernel syzygy_fourth_factor
end NLA.MF14Degree44
