/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

The finite summation-by-parts theorem is reused unchanged from MI24's
ScalarLogMajorization, authored by George Stepaniants with Codex agent /root.
Weights a/(1+a) decrease with the positive descending source sequence. C16
then transfers the prefix-product inequalities to the products of 1+a.
-/
import NLA.MI28.LogOneAddTangent
import NLA.MI24.ScalarLogMajorization

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace NLA.MI28

/-- C17: positive descending weak log-majorization gives the determinant product bound. -/
theorem product_one_add_le {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hsort : Antitone a)
    (hprefix : WeakLogMajorized a b) :
    (∏ i : Fin n, (1 + a i)) ≤ ∏ i : Fin n, (1 + b i) := by
  have hlogs : ∀ j (hj : j ≤ n),
      (∑ i : Fin j, (Real.log (a (Fin.castLE hj i)) -
        Real.log (b (Fin.castLE hj i)))) ≤ 0 := by
    intro j hj
    have hlog := Real.log_le_log
      (Finset.prod_pos (fun i _ => ha (Fin.castLE hj i))) (hprefix j hj)
    -- Unfold the frozen prefix products before applying the finite-product log identity.
    dsimp only [prefixProduct] at hlog
    rw [Real.log_prod (fun i _ => (ha (Fin.castLE hj i)).ne'),
      Real.log_prod (fun i _ => (hb (Fin.castLE hj i)).ne')] at hlog
    rw [Finset.sum_sub_distrib]
    exact sub_nonpos.mpr hlog
  have hw : ∀ i, 0 ≤ a i / (1 + a i) := fun i =>
    div_nonneg (ha i).le (by linarith [ha i])
  have hm : Antitone (fun i => a i / (1 + a i)) := by
    intro i j hij
    apply (div_le_div_iff₀ (by linarith [ha j] : 0 < 1 + a j)
      (by linarith [ha i] : 0 < 1 + a i)).mpr
    nlinarith [hsort hij]
  have hweighted := NLA.MI24.weighted_prefix_sum_nonpos
    (fun i => a i / (1 + a i)) (fun i => Real.log (a i) - Real.log (b i)) hw hm hlogs
  have hsum : (∑ i : Fin n, (Real.log (1 + a i) - Real.log (1 + b i))) ≤ 0 :=
    (Finset.sum_le_sum (fun i _ => log_one_add_tangent (a i) (b i) (ha i) (hb i))).trans
      hweighted
  have ha1 : ∀ i, 0 < 1 + a i := fun i => by linarith [ha i]
  have hb1 : ∀ i, 0 < 1 + b i := fun i => by linarith [hb i]
  apply (Real.log_le_log_iff (Finset.prod_pos (fun i _ => ha1 i))
    (Finset.prod_pos (fun i _ => hb1 i))).mp
  rw [Real.log_prod (fun i _ => (ha1 i).ne'), Real.log_prod (fun i _ => (hb1 i).ne')]
  exact sub_nonpos.mp (by simpa only [Finset.sum_sub_distrib] using hsum)

end NLA.MI28
