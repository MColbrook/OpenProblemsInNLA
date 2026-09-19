import NLA.MF14Degree44.Mod3Lists

set_option autoImplicit false
open Polynomial
open scoped BigOperators Matrix
noncomputable section
namespace NLA.MF14Degree44
namespace Mod3Certificate

theorem product_entry_cast (i j : Fin 45) :
    (tableJacobianMod3 * tableInverseMod3) i j = (productEntryNat i j : ZMod 3) := by
  simp only [Matrix.mul_apply, tableJacobianMod3, tableInverseMod3, productEntryNat,
    ← Fin.sum_univ_def, Nat.cast_sum, Nat.cast_mul]

theorem matrix_entry_of_natural_residue (i j : Fin 45)
    (h : productEntryNat i j % 3 = if i = j then 1 else 0) :
    (tableJacobianMod3 * tableInverseMod3) i j =
      (1 : Matrix (Fin 45) (Fin 45) (ZMod 3)) i j := by
  rw [product_entry_cast, Matrix.one_apply]
  have hh : ((productEntryNat i j % 3 : ℕ) : ZMod 3) =
      if i = j then 1 else 0 := by
    rw [h]
    split_ifs <;> rfl
  simpa only [ZMod.natCast_mod] using hh

#print axioms product_entry_cast
#assert_trust kernel product_entry_cast
#print axioms matrix_entry_of_natural_residue
#assert_trust kernel matrix_entry_of_natural_residue

end Mod3Certificate
end NLA.MF14Degree44
