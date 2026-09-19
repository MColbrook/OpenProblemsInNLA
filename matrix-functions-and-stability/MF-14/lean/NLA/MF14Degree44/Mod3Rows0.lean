import NLA.MF14Degree44.Mod3Lists

set_option autoImplicit false
open Polynomial
open scoped BigOperators Matrix
noncomputable section
namespace NLA.MF14Degree44
namespace Mod3Certificate

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_0 : ∀ j : Fin 45,
    productEntryNat 0 j % 3 = if (0 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_0
#assert_trust kernel natural_inverse_row_0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_1 : ∀ j : Fin 45,
    productEntryNat 1 j % 3 = if (1 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_1
#assert_trust kernel natural_inverse_row_1

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_2 : ∀ j : Fin 45,
    productEntryNat 2 j % 3 = if (2 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_2
#assert_trust kernel natural_inverse_row_2

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_3 : ∀ j : Fin 45,
    productEntryNat 3 j % 3 = if (3 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_3
#assert_trust kernel natural_inverse_row_3

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_4 : ∀ j : Fin 45,
    productEntryNat 4 j % 3 = if (4 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_4
#assert_trust kernel natural_inverse_row_4

end Mod3Certificate
end NLA.MF14Degree44
