import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

def vandermondeDegree (k : ℕ) : ℕ := ∑ i : Fin k, i.val

theorem twice_vandermondeDegree (k : ℕ) :
    2 * vandermondeDegree k = k * (k - 1) := by
  induction k with
  | zero => simp [vandermondeDegree]
  | succ k ih =>
    have hs : vandermondeDegree (k + 1) = vandermondeDegree k + k := by
      simp only [vandermondeDegree, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    rw [hs, Nat.mul_add, ih]
    cases k <;> simp <;> ring

theorem vandermonde_mul_scalar (k : ℕ) (u : Fin k → ℂ) (c : ℂ) :
    (Matrix.vandermonde (fun i => c * u i)).det =
      c ^ vandermondeDegree k * (Matrix.vandermonde u).det := by
  have hm : Matrix.vandermonde (fun i => c * u i) =
      Matrix.of (fun i j => c ^ j.val * Matrix.vandermonde u i j) := by
    ext i j
    simp only [Matrix.vandermonde_apply, Matrix.of_apply, mul_pow]
  rw [hm, Matrix.det_mul_row, Finset.prod_pow_eq_pow_sum]
  rfl

theorem vandermonde_one_add_mul (k : ℕ) (u : Fin k → ℂ) (c : ℂ) :
    (Matrix.vandermonde (fun i => 1 + c * u i)).det =
      c ^ vandermondeDegree k * (Matrix.vandermonde u).det := by
  have heq : (fun i => 1 + c * u i) = (fun i => c * u i + 1) := by
    funext i
    ring
  rw [heq, Matrix.det_vandermonde_add, vandermonde_mul_scalar]

#print axioms twice_vandermondeDegree
#print axioms vandermonde_mul_scalar
#print axioms vandermonde_one_add_mul

end MF21Restart
