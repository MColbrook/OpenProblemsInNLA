import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas

/-!
The coefficient-extraction step needed in a mesh uniqueness proof.
This does not establish mesh density, continuity of the manuscript's
coefficients, or the Toeplitz asymptotic estimates. Those are distinct inputs.
-/

open Filter Asymptotics
open scoped Topology

set_option backward.isDefEq.respectTransparency.types false

namespace MF21Audit

/-- Once all preceding coefficients agree, subtracting order-`k` expansions
produces this estimate. Dividing by the nonzero mesh power identifies the next
coefficient from its limit. -/
theorem coefficient_unique_of_weighted_bigO
    (a b h : ℕ → ℝ) (A B : ℝ) (k : ℕ)
    (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B))
    (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ᶠ n in atTop, h n ≠ 0)
    (he : (fun n ↦ (a n - b n) * h n ^ k) =O[atTop]
      (fun n ↦ h n ^ (k + 1))) : A = B := by
  have hp : (fun n ↦ h n ^ (k + 1)) =o[atTop] (fun n ↦ h n ^ k) :=
    (isLittleO_pow_pow (Nat.lt_succ_self k)).comp_tendsto hh
  have hz := (he.trans_isLittleO hp).tendsto_div_nhds_zero
  have hz' : Tendsto (fun n ↦ a n - b n) atTop (𝓝 0) := by
    apply hz.congr'
    filter_upwards [hne] with n hn
    exact mul_div_cancel_right₀ (a n - b n) (pow_ne_zero k hn)
  exact sub_eq_zero.mp (tendsto_nhds_unique (ha.sub hb) hz')

/-- Version for coefficient functions sampled along a convergent sequence.
In MF-21 the samples would be x_(n,j(n)) → x. -/
theorem continuous_coefficient_unique
    (a b : ℝ → ℝ) (xseq h : ℕ → ℝ) (x : ℝ) (k : ℕ)
    (ha : ContinuousAt a x) (hb : ContinuousAt b x)
    (hx : Tendsto xseq atTop (𝓝 x))
    (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ᶠ n in atTop, h n ≠ 0)
    (he : (fun n ↦ (a (xseq n) - b (xseq n)) * h n ^ k) =O[atTop]
      (fun n ↦ h n ^ (k + 1))) : a x = b x := by
  exact coefficient_unique_of_weighted_bigO (fun n ↦ a (xseq n))
    (fun n ↦ b (xseq n)) h (a x) (b x) k
    (ha.tendsto.comp hx) (hb.tendsto.comp hx) hh hne he

/-- Uniqueness of a finite expansion along a family of convergent meshes.
Every hypothesis is explicit: continuity, mesh convergence/membership and the
two expansion estimates through each truncation order. This theorem does not
assert that the particular MF-21 eigenvalue family satisfies those hypotheses.
-/
theorem expansion_unique_on_mesh
    (S : Set ℝ) (mesh : ℝ → ℕ → ℝ) (h : ℕ → ℝ)
    (f : ℝ → ℕ → ℝ) (a b : ℕ → ℝ → ℝ) (N : ℕ)
    (hmesh : ∀ x ∈ S, Tendsto (mesh x) atTop (𝓝 x))
    (hmem : ∀ x ∈ S, ∀ n, mesh x n ∈ S)
    (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ᶠ n in atTop, h n ≠ 0)
    (ha : ∀ k ≤ N, ∀ x ∈ S, ContinuousAt (a k) x)
    (hb : ∀ k ≤ N, ∀ x ∈ S, ContinuousAt (b k) x)
    (hea : ∀ k ≤ N, ∀ x ∈ S,
      (fun n ↦ f x n - ∑ i ∈ Finset.range (k + 1), a i (mesh x n) * h n ^ i)
        =O[atTop] (fun n ↦ h n ^ (k + 1)))
    (heb : ∀ k ≤ N, ∀ x ∈ S,
      (fun n ↦ f x n - ∑ i ∈ Finset.range (k + 1), b i (mesh x n) * h n ^ i)
        =O[atTop] (fun n ↦ h n ^ (k + 1))) :
    ∀ k ≤ N, ∀ x ∈ S, a k x = b k x := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk x hx
    apply continuous_coefficient_unique (a k) (b k) (mesh x) h x k
      (ha k hk x hx) (hb k hk x hx) (hmesh x hx) hh hne
    have hdiff := (heb k hk x hx).sub (hea k hk x hx)
    apply hdiff.congr' _ (Filter.EventuallyEq.refl _ _)
    apply Filter.Eventually.of_forall
    intro n
    have heq : (∑ i ∈ Finset.range k, a i (mesh x n) * h n ^ i) =
        ∑ i ∈ Finset.range k, b i (mesh x n) * h n ^ i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [ih i (Finset.mem_range.mp hi) (Nat.le_trans (Nat.le_of_lt
        (Finset.mem_range.mp hi)) hk) (mesh x n) (hmem x hx n)]
    simp only [Finset.sum_range_succ]
    rw [heq]
    ring

/-- The complete uniqueness induction needs only the top-order difference
estimate. Continuity is within S and mesh membership is only eventual. -/
theorem top_expansion_unique_on_mesh
    (S : Set ℝ) (mesh : ℝ → ℕ → ℝ) (h : ℕ → ℝ)
    (a b : ℕ → ℝ → ℝ) (N : ℕ)
    (hmesh : ∀ x ∈ S, Tendsto (mesh x) atTop (𝓝 x))
    (hmem : ∀ x ∈ S, ∀ᶠ n in atTop, mesh x n ∈ S)
    (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ᶠ n in atTop, h n ≠ 0)
    (ha : ∀ k ≤ N, ContinuousOn (a k) S)
    (hb : ∀ k ≤ N, ContinuousOn (b k) S)
    (he : ∀ x ∈ S,
      (fun n ↦ ∑ i ∈ Finset.range (N + 1),
        (a i (mesh x n) - b i (mesh x n)) * h n ^ i)
        =O[atTop] (fun n ↦ h n ^ (N + 1))) :
    ∀ k ≤ N, ∀ x ∈ S, a k x = b k x := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk x hx
    have hxwithin : Tendsto (mesh x) atTop (𝓝[S] x) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (mesh x)
        (hmesh x hx) (hmem x hx)
    have hlim (i : ℕ) (hi : i ≤ N) :
        Tendsto (fun n ↦ a i (mesh x n) - b i (mesh x n)) atTop
          (𝓝 (a i x - b i x)) :=
      ((ha i hi x hx).tendsto.comp hxwithin).sub
        ((hb i hi x hx).tendsto.comp hxwithin)
    have hwhole : (fun n ↦ ∑ i ∈ Finset.range (N + 1),
        (a i (mesh x n) - b i (mesh x n)) * h n ^ i)
        =o[atTop] (fun n ↦ h n ^ k) :=
      (he x hx).trans_isLittleO
        ((isLittleO_pow_pow (Nat.lt_succ_of_le hk)).comp_tendsto hh)
    have hothers : (fun n ↦ ∑ i ∈ (Finset.range (N + 1)).erase k,
        (a i (mesh x n) - b i (mesh x n)) * h n ^ i)
        =o[atTop] (fun n ↦ h n ^ k) := by
      suffices H : (∑ i ∈ (Finset.range (N + 1)).erase k,
          fun n ↦ (a i (mesh x n) - b i (mesh x n)) * h n ^ i)
          =o[atTop] (fun n ↦ h n ^ k) by
        exact H.congr_left (fun n ↦ Finset.sum_apply n _ _)
      apply IsLittleO.sum
      intro i hi
      obtain ⟨hik, hi⟩ := Finset.mem_erase.mp hi
      have hiN : i ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rcases lt_or_gt_of_ne hik with hil | hir
      · apply (isLittleO_zero (fun n ↦ h n ^ k) atTop).congr'
          _ (Filter.EventuallyEq.refl _ _)
        filter_upwards [hmem x hx] with n hn
        rw [ih i hil hiN (mesh x n) hn]
        simp
      · have hbounded : (fun n ↦ a i (mesh x n) - b i (mesh x n))
            =O[atTop] (fun _ ↦ (1 : ℝ)) :=
          isBigO_const_of_tendsto (hlim i hiN) one_ne_zero
        simpa only [one_mul, Function.comp_apply] using hbounded.mul_isLittleO
          ((isLittleO_pow_pow hir).comp_tendsto hh)
    have hlead : (fun n ↦ (a k (mesh x n) - b k (mesh x n)) * h n ^ k)
        =o[atTop] (fun n ↦ h n ^ k) := by
      apply (hwhole.sub hothers).congr'
        _ (Filter.EventuallyEq.refl _ _)
      apply Filter.Eventually.of_forall
      intro n
      dsimp only
      rw [← Finset.sum_erase_add _ _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))]
      ring
    have hz := hlead.tendsto_div_nhds_zero
    have hz' : Tendsto (fun n ↦ a k (mesh x n) - b k (mesh x n))
        atTop (𝓝 0) := by
      apply hz.congr'
      filter_upwards [hne] with n hn
      exact mul_div_cancel_right₀ _ (pow_ne_zero k hn)
    exact sub_eq_zero.mp (tendsto_nhds_unique (hlim k hk) hz')

end MF21Audit

#print axioms MF21Audit.coefficient_unique_of_weighted_bigO
#print axioms MF21Audit.continuous_coefficient_unique

#print axioms MF21Audit.expansion_unique_on_mesh

#print axioms MF21Audit.top_expansion_unique_on_mesh
