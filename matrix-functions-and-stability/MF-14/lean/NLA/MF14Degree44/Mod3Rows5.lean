import NLA.MF14Degree44.Mod3Lists

set_option autoImplicit false
open Polynomial
open scoped BigOperators Matrix
noncomputable section
namespace NLA.MF14Degree44
namespace Mod3Certificate

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_25 : ∀ j : Fin 45,
    productEntryNat 25 j % 3 = if (25 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_25
#assert_trust kernel natural_inverse_row_25

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_26 : ∀ j : Fin 45,
    productEntryNat 26 j % 3 = if (26 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_26
#assert_trust kernel natural_inverse_row_26

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_27 : ∀ j : Fin 45,
    productEntryNat 27 j % 3 = if (27 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_27
#assert_trust kernel natural_inverse_row_27

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_28 : ∀ j : Fin 45,
    productEntryNat 28 j % 3 = if (28 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_28
#assert_trust kernel natural_inverse_row_28

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_29 : ∀ j : Fin 45,
    productEntryNat 29 j % 3 = if (29 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_29
#assert_trust kernel natural_inverse_row_29

end Mod3Certificate
end NLA.MF14Degree44
