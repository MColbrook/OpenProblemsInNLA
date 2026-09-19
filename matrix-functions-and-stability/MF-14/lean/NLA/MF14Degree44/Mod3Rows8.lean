import NLA.MF14Degree44.Mod3Lists

set_option autoImplicit false
open Polynomial
open scoped BigOperators Matrix
noncomputable section
namespace NLA.MF14Degree44
namespace Mod3Certificate

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_40 : ∀ j : Fin 45,
    productEntryNat 40 j % 3 = if (40 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_40
#assert_trust kernel natural_inverse_row_40

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_41 : ∀ j : Fin 45,
    productEntryNat 41 j % 3 = if (41 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_41
#assert_trust kernel natural_inverse_row_41

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_42 : ∀ j : Fin 45,
    productEntryNat 42 j % 3 = if (42 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_42
#assert_trust kernel natural_inverse_row_42

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_43 : ∀ j : Fin 45,
    productEntryNat 43 j % 3 = if (43 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_43
#assert_trust kernel natural_inverse_row_43

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_44 : ∀ j : Fin 45,
    productEntryNat 44 j % 3 = if (44 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_44
#assert_trust kernel natural_inverse_row_44

end Mod3Certificate
end NLA.MF14Degree44
