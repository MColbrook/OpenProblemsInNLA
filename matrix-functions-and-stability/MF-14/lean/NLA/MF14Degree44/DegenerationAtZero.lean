/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Marcus Webb retains credit for the
mathematical construction and symbolic certificate.
-/
import NLA.MF14Degree44.Degeneration
import Mathlib.Tactic.Ring
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open Polynomial
namespace NLA.MF14Degree44

/-- Exact substitution in the full polynomial extension at the singular parameter. -/
theorem degeneration_at_zero (alpha eta gamma : ℂ) :
    degenerationZ alpha eta gamma 0 = X ^ 12 + C (3 * alpha - 4 * gamma ^ 2) * X ^ 11 := by
  simp [degenerationZ, borderC, borderD, map_add, map_mul, map_neg, map_sub, map_pow, map_ofNat] <;> ring

#print axioms degeneration_at_zero
#assert_trust kernel degeneration_at_zero

end NLA.MF14Degree44
