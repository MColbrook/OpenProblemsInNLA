import NLA.MF14Degree44.Mod3Lists

set_option autoImplicit false
open Polynomial
open scoped BigOperators Matrix
noncomputable section
namespace NLA.MF14Degree44
namespace Mod3Certificate

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_20 : ∀ j : Fin 45,
    productEntryNat 20 j % 3 = if (20 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_20
#assert_trust kernel natural_inverse_row_20

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_21 : ∀ j : Fin 45,
    productEntryNat 21 j % 3 = if (21 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_21
#assert_trust kernel natural_inverse_row_21

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_22 : ∀ j : Fin 45,
    productEntryNat 22 j % 3 = if (22 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_22
#assert_trust kernel natural_inverse_row_22

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_23 : ∀ j : Fin 45,
    productEntryNat 23 j % 3 = if (23 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_23
#assert_trust kernel natural_inverse_row_23

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_24 : ∀ j : Fin 45,
    productEntryNat 24 j % 3 = if (24 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_24
#assert_trust kernel natural_inverse_row_24

end Mod3Certificate
end NLA.MF14Degree44
