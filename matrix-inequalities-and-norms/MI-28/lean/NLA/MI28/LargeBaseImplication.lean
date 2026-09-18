/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

Join the Ghabries-range order core to the exact product-modulus identity.
This is the universal OrderImplication needed for C12; the common positive
scalar norm-normalization argument can also serve the small-base C11 route.
All exponent endpoints 0 <= p <= 2 are retained in this internal helper.
-/
import NLA.MI28.LargeBaseOrder
import NLA.MI28.ModulusPowers

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI28

/-- The complete large-base universal order implication, including p=0. -/
lemma large_base_implication (k p : ℝ) (hk : 2 ≤ k)
    (hp0 : 0 ≤ p) (hp2 : p ≤ 2) : OrderImplication k p := by
  intro n _ A B hA hB h
  have hgram : spectralPower (B * spectralPower A 2 * B) (p / 2) ≤
      spectralPower A k := by
    rw [← product_modulus_power A B hA hB p hp0]
    exact h
  have hcore : NLA.MI24.spectralPower B p ≤ NLA.MI24.spectralPower A (k - p) := by
    apply large_base_sandwich_order A B hA hB k p hk hp0 hp2
    -- The internal reused power and the frozen MI28 power are the same CFC.rpow.
    simpa only [spectralPower, NLA.MI24.spectralPower] using hgram
  simpa only [spectralPower, NLA.MI24.spectralPower] using hcore

end NLA.MI28
