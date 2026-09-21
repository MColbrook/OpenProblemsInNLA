import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Real.Basic

/-!
Interlacing of ordered diagonal quadratic forms under a norm-preserving
linear inclusion. The proof is a dimension/kernel argument. Its two form
identities still have to be discharged for an actual matrix compression.
See `DIAGONAL_INTERLACING_STATEMENTS.md`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

def initialCoordinateEmbedding (n N : ℕ) (hnN : n ≤ N) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin N → ℝ) where
  toFun x i := if hi : i.val < n then x ⟨i.val, hi⟩ else 0
  map_add' x y := by
    funext i
    by_cases hi : i.val < n <;> simp [hi]
  map_smul' c x := by
    funext i
    by_cases hi : i.val < n <;> simp [hi]

theorem initialCoordinateEmbedding_apply_castLE
    (n N : ℕ) (hnN : n ≤ N) (x : Fin n → ℝ) (i : Fin n) :
    initialCoordinateEmbedding n N hnN x (Fin.castLE hnN i) = x i := by
  simp [initialCoordinateEmbedding, i.isLt]

theorem initialCoordinateEmbedding_apply_of_le
    (n N : ℕ) (hnN : n ≤ N) (x : Fin n → ℝ) (i : Fin N) (hi : n ≤ i.val) :
    initialCoordinateEmbedding n N hnN x i = 0 := by
  simp [initialCoordinateEmbedding, not_lt.mpr hi]

private theorem diagonal_isometry_lower
    (n N : ℕ) (hnN : n ≤ N) (a : Fin n → ℝ) (b : Fin N → ℝ)
    (ha : Monotone a) (hb : Monotone b)
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin N → ℝ))
    (hnorm : ∀ x, (∑ i : Fin N, (L x i) ^ 2) = ∑ i : Fin n, (x i) ^ 2)
    (hform : ∀ x, (∑ i : Fin N, b i * (L x i) ^ 2) =
      ∑ i : Fin n, a i * (x i) ^ 2) (j : Fin n) :
    b (Fin.castLE hnN j) ≤ a j := by
  classical
  have hj := j.isLt
  let E := initialCoordinateEmbedding (j.val + 1) n (by omega)
  let P : (Fin (j.val + 1) → ℝ) →ₗ[ℝ] (Fin j.val → ℝ) :=
    { toFun := fun v i => L (E v) ⟨i.val, by have := i.isLt; omega⟩
      map_add' := by
        intro v w
        funext i
        simp only [map_add, Pi.add_apply]
      map_smul' := by
        intro c v
        funext i
        simp only [map_smul, Pi.smul_apply, RingHom.id_apply] }
  have hker : LinearMap.ker P ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨v, hv, hv0⟩ := (LinearMap.ker P).ne_bot_iff.mp hker
  have hvP : P v = 0 := LinearMap.mem_ker.mp hv
  let x := E v
  have hx0 : x ≠ 0 := by
    intro hx
    apply hv0
    funext i
    have hi := congrFun hx (Fin.castLE (show j.val + 1 ≤ n by omega) i)
    simpa only [x, E, initialCoordinateEmbedding_apply_castLE, Pi.zero_apply] using hi
  have hpositive : 0 < ∑ i : Fin n, (x i) ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
    exact Finset.sum_pos' (fun i _ => sq_nonneg (x i))
      ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
  have hzero (i : Fin N) (hi : i.val < j.val) : L x i = 0 := by
    have h := congrFun hvP (⟨i.val, hi⟩ : Fin j.val)
    exact h
  have hcmp : b (Fin.castLE hnN j) * (∑ i : Fin n, (x i) ^ 2) ≤
      a j * (∑ i : Fin n, (x i) ^ 2) := by
    calc
      b (Fin.castLE hnN j) * (∑ i : Fin n, (x i) ^ 2) =
          b (Fin.castLE hnN j) * (∑ i : Fin N, (L x i) ^ 2) := by rw [hnorm]
      _ ≤ ∑ i : Fin N, b i * (L x i) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i.val < j.val
        · simp [hzero i hi]
        · apply mul_le_mul_of_nonneg_right (hb ?_) (sq_nonneg _)
          change j.val ≤ i.val
          omega
      _ = ∑ i : Fin n, a i * (x i) ^ 2 := hform x
      _ ≤ a j * (∑ i : Fin n, (x i) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i.val < j.val + 1
        · apply mul_le_mul_of_nonneg_right (ha ?_) (sq_nonneg _)
          change i.val ≤ j.val
          omega
        · have hxi : x i = 0 :=
            initialCoordinateEmbedding_apply_of_le (j.val + 1) n (by omega) v i (by omega)
          simp [hxi]
  exact (mul_le_mul_iff_of_pos_right hpositive).mp hcmp

private def reverseCoordinates (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun x i := x i.rev
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Repeated values are allowed. Both inequalities are proved from the
two exact form identities and finite-dimensional linear algebra. -/
theorem diagonal_isometry_interlacing
    (n N : ℕ) (hnN : n ≤ N) (a : Fin n → ℝ) (b : Fin N → ℝ)
    (ha : Monotone a) (hb : Monotone b)
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin N → ℝ))
    (hnorm : ∀ x, (∑ i : Fin N, (L x i) ^ 2) = ∑ i : Fin n, (x i) ^ 2)
    (hform : ∀ x, (∑ i : Fin N, b i * (L x i) ^ 2) =
      ∑ i : Fin n, a i * (x i) ^ 2) (j : Fin n) :
    b (Fin.castLE hnN j) ≤ a j ∧
      a j ≤ b ⟨j.val + (N - n), by have := j.isLt; omega⟩ := by
  refine ⟨diagonal_isometry_lower n N hnN a b ha hb L hnorm hform j, ?_⟩
  let ar : Fin n → ℝ := fun i => -a i.rev
  let br : Fin N → ℝ := fun i => -b i.rev
  let Lr := (reverseCoordinates N).comp (L.comp (reverseCoordinates n))
  have har : Monotone ar := by
    intro i k hik
    exact neg_le_neg (ha (Fin.rev_le_rev.mpr hik))
  have hbr : Monotone br := by
    intro i k hik
    exact neg_le_neg (hb (Fin.rev_le_rev.mpr hik))
  have hnormr (x : Fin n → ℝ) :
      (∑ i : Fin N, (Lr x i) ^ 2) = ∑ i : Fin n, (x i) ^ 2 := by
    change (∑ i : Fin N, (L (fun k => x k.rev) i.rev) ^ 2) = _
    calc
      _ = ∑ i : Fin N, (L (fun k => x k.rev) i) ^ 2 :=
        Equiv.sum_comp Fin.revPerm _
      _ = ∑ i : Fin n, (x i.rev) ^ 2 := hnorm _
      _ = ∑ i : Fin n, (x i) ^ 2 := by
        simpa only [Fin.revPerm_apply] using
          (Equiv.sum_comp Fin.revPerm (fun i : Fin n => (x i) ^ 2))
  have hformr (x : Fin n → ℝ) :
      (∑ i : Fin N, br i * (Lr x i) ^ 2) = ∑ i : Fin n, ar i * (x i) ^ 2 := by
    change (∑ i : Fin N, -b i.rev * (L (fun k => x k.rev) i.rev) ^ 2) =
      ∑ i : Fin n, -a i.rev * (x i) ^ 2
    calc
      _ = -(∑ i : Fin N, b i * (L (fun k => x k.rev) i) ^ 2) := by
        simp only [neg_mul, Finset.sum_neg_distrib]
        congr 1
        simpa only [Fin.revPerm_apply] using
          (Equiv.sum_comp Fin.revPerm
            (fun i : Fin N => b i * (L (fun k => x k.rev) i) ^ 2))
      _ = -(∑ i : Fin n, a i * (x i.rev) ^ 2) := congrArg Neg.neg (hform _)
      _ = ∑ i : Fin n, -a i.rev * (x i) ^ 2 := by
        have h := Equiv.sum_comp Fin.revPerm (fun i : Fin n => a i * (x i.rev) ^ 2)
        simp only [Fin.revPerm_apply, Fin.rev_rev] at h
        simp only [neg_mul, Finset.sum_neg_distrib]
        exact congrArg Neg.neg h.symm
  have h := diagonal_isometry_lower n N hnN ar br har hbr Lr hnormr hformr j.rev
  have hrev : (Fin.castLE hnN j.rev).rev =
      (⟨j.val + (N - n), by have := j.isLt; omega⟩ : Fin N) := by
    apply Fin.ext
    change N - (n - (j.val + 1) + 1) = j.val + (N - n)
    have := j.isLt
    omega
  change -b (Fin.castLE hnN j.rev).rev ≤ -a j.rev.rev at h
  rw [hrev, Fin.rev_rev] at h
  exact neg_le_neg_iff.mp h

#print axioms diagonal_isometry_interlacing

end MF21Restart
