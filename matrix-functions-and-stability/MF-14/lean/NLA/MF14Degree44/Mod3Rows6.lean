import NLA.MF14Degree44.Mod3Lists

set_option autoImplicit false
open Polynomial
open scoped BigOperators Matrix
noncomputable section
namespace NLA.MF14Degree44
namespace Mod3Certificate

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_30 : ∀ j : Fin 45,
    productEntryNat 30 j % 3 = if (30 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_30
#assert_trust kernel natural_inverse_row_30

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_31 : ∀ j : Fin 45,
    productEntryNat 31 j % 3 = if (31 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_31
#assert_trust kernel natural_inverse_row_31

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_32 : ∀ j : Fin 45,
    productEntryNat 32 j % 3 = if (32 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_32
#assert_trust kernel natural_inverse_row_32

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_33 : ∀ j : Fin 45,
    productEntryNat 33 j % 3 = if (33 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_33
#assert_trust kernel natural_inverse_row_33

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem natural_inverse_row_34 : ∀ j : Fin 45,
    productEntryNat 34 j % 3 = if (34 : Fin 45) = j then 1 else 0 := by
  decide +kernel

#print axioms natural_inverse_row_34
#assert_trust kernel natural_inverse_row_34

end Mod3Certificate
end NLA.MF14Degree44
