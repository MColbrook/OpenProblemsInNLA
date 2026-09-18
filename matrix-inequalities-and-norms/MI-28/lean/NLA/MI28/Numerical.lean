/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

Kernel-trust setup and the single fixed-constant proof pattern follow the
accepted MF05 Numerical module, authored by George Stepaniants with substantial
OpenAI Codex assistance. Only the dyadic half is certified. There are no
matrix-entry, dimension, spectral, or real-parameter grids.
ModulusPowers consumes the certified nonnegative-half hypothesis in CFC power
composition, so this certificate lies on the C02 mathematical dependency path.
-/
import NLA.MI28.Definitions
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MI28

/-- C01: the sole fixed numerical target, proved by kernel-checked certificates. -/
theorem half_exponent_interval : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 := by
  constructor <;> interval_decide (trust := kernel)

#print axioms half_exponent_interval
#assert_trust kernel half_exponent_interval

end NLA.MI28
