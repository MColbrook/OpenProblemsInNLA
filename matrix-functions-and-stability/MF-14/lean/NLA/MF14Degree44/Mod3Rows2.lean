import NLA.MF14Degree44.Mod3Lists

set_option autoImplicit false
open Polynomial
open scoped BigOperators Matrix
noncomputable section
namespace NLA.MF14Degree44
namespace Mod3Certificate

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_10 : ∀ j : Fin 45,
    productEntryNat 10 j % 3 = if (10 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_10
#assert_trust kernel natural_inverse_row_10

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_11 : ∀ j : Fin 45,
    productEntryNat 11 j % 3 = if (11 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_11
#assert_trust kernel natural_inverse_row_11

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_12 : ∀ j : Fin 45,
    productEntryNat 12 j % 3 = if (12 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_12
#assert_trust kernel natural_inverse_row_12

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_13 : ∀ j : Fin 45,
    productEntryNat 13 j % 3 = if (13 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_13
#assert_trust kernel natural_inverse_row_13

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_14 : ∀ j : Fin 45,
    productEntryNat 14 j % 3 = if (14 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_14
#assert_trust kernel natural_inverse_row_14

end Mod3Certificate
end NLA.MF14Degree44
