import NLA.MF14Degree44.Mod3Lists

set_option autoImplicit false
open Polynomial
open scoped BigOperators Matrix
noncomputable section
namespace NLA.MF14Degree44
namespace Mod3Certificate

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_5 : ∀ j : Fin 45,
    productEntryNat 5 j % 3 = if (5 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_5
#assert_trust kernel natural_inverse_row_5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_6 : ∀ j : Fin 45,
    productEntryNat 6 j % 3 = if (6 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_6
#assert_trust kernel natural_inverse_row_6

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_7 : ∀ j : Fin 45,
    productEntryNat 7 j % 3 = if (7 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_7
#assert_trust kernel natural_inverse_row_7

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_8 : ∀ j : Fin 45,
    productEntryNat 8 j % 3 = if (8 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_8
#assert_trust kernel natural_inverse_row_8

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_9 : ∀ j : Fin 45,
    productEntryNat 9 j % 3 = if (9 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_9
#assert_trust kernel natural_inverse_row_9

end Mod3Certificate
end NLA.MF14Degree44
