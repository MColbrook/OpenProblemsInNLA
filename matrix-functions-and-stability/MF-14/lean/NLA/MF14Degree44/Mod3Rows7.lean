import NLA.MF14Degree44.Mod3Lists

set_option autoImplicit false
open Polynomial
open scoped BigOperators Matrix
noncomputable section
namespace NLA.MF14Degree44
namespace Mod3Certificate

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_35 : ∀ j : Fin 45,
    productEntryNat 35 j % 3 = if (35 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_35
#assert_trust kernel natural_inverse_row_35

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_36 : ∀ j : Fin 45,
    productEntryNat 36 j % 3 = if (36 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_36
#assert_trust kernel natural_inverse_row_36

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_37 : ∀ j : Fin 45,
    productEntryNat 37 j % 3 = if (37 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_37
#assert_trust kernel natural_inverse_row_37

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_38 : ∀ j : Fin 45,
    productEntryNat 38 j % 3 = if (38 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_38
#assert_trust kernel natural_inverse_row_38

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_39 : ∀ j : Fin 45,
    productEntryNat 39 j % 3 = if (39 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_39
#assert_trust kernel natural_inverse_row_39

end Mod3Certificate
end NLA.MF14Degree44
