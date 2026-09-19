import NLA.MF14Degree44.Mod3Lists

set_option autoImplicit false
open Polynomial
open scoped BigOperators Matrix
noncomputable section
namespace NLA.MF14Degree44
namespace Mod3Certificate

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_15 : ∀ j : Fin 45,
    productEntryNat 15 j % 3 = if (15 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_15
#assert_trust kernel natural_inverse_row_15

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_16 : ∀ j : Fin 45,
    productEntryNat 16 j % 3 = if (16 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_16
#assert_trust kernel natural_inverse_row_16

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_17 : ∀ j : Fin 45,
    productEntryNat 17 j % 3 = if (17 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_17
#assert_trust kernel natural_inverse_row_17

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_18 : ∀ j : Fin 45,
    productEntryNat 18 j % 3 = if (18 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_18
#assert_trust kernel natural_inverse_row_18

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_19 : ∀ j : Fin 45,
    productEntryNat 19 j % 3 = if (19 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_19
#assert_trust kernel natural_inverse_row_19

end Mod3Certificate
end NLA.MF14Degree44
