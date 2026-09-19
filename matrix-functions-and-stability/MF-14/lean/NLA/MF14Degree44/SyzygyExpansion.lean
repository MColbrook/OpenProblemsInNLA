/- Generic polynomial expansion; certificate coefficients remain independent.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; substantial Codex assistance. -/
import NLA.MF14Degree44.DegenerationCoefficientData
import Mathlib.Tactic.Ring
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
open scoped BigOperators
namespace NLA.MF14Degree44

theorem syzygy_polynomial_expansion (alpha eta gamma s : ℂ) (c : Fin 5 → ℂ) :
    (∑ i : Fin 5, C (c i) * syzygyBasis alpha eta gamma s i) =
      syzygyLowPartFor alpha eta gamma s c +
      C (syzygyMiddle7For alpha eta gamma s c) * X ^ 7 +
      C (syzygyMiddle8For alpha eta gamma s c) * X ^ 8 +
      C (syzygyMiddle9For alpha eta gamma s c) * X ^ 9 +
      C (syzygyMiddle10For alpha eta gamma s c) * X ^ 10 +
      syzygyHighPartFor alpha eta gamma s c := by
  simp [syzygyBasis, syzygyLowPartFor, syzygyMiddle7For, syzygyMiddle8For,
    syzygyMiddle9For, syzygyMiddle10For, syzygyHighPartFor, syzygyR5, syzygyR6,
    Q, Rparam, Fin.sum_univ_succ, map_add, map_mul, map_pow, map_ofNat] <;> ring

#print axioms syzygy_polynomial_expansion
#assert_trust kernel syzygy_polynomial_expansion
end NLA.MF14Degree44
