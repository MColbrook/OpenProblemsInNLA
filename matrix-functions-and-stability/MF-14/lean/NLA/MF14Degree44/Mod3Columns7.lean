import NLA.MF14Degree44.Mod3Lists

set_option autoImplicit false
open Polynomial
open scoped BigOperators Matrix
noncomputable section
namespace NLA.MF14Degree44
namespace Mod3Certificate

theorem column_expansion_35 : integerDerivativeColumns 35 = C (1 : ℤ) * X ^ 36 + C (1 : ℤ) * X ^ 39 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_35 : ∀ i : Fin 45,
    tableIntegerJacobian i 35 = (if i.val = 36 then (1 : ℤ) else 0) + (if i.val = 39 then (1 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_35 (i : Fin 45) :
    integerJacobian i 35 = tableIntegerJacobian i 35 := by
  unfold integerJacobian
  rw [column_expansion_35, table_column_values_35]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_35
#assert_trust kernel column_table_match_35

theorem column_expansion_36 : integerDerivativeColumns 36 = C (1 : ℤ) * X ^ 0 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_36 : ∀ i : Fin 45,
    tableIntegerJacobian i 36 = (if i.val = 0 then (1 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_36 (i : Fin 45) :
    integerJacobian i 36 = tableIntegerJacobian i 36 := by
  unfold integerJacobian
  rw [column_expansion_36, table_column_values_36]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_36
#assert_trust kernel column_table_match_36

theorem column_expansion_37 : integerDerivativeColumns 37 = C (1 : ℤ) * X ^ 1 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_37 : ∀ i : Fin 45,
    tableIntegerJacobian i 37 = (if i.val = 1 then (1 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_37 (i : Fin 45) :
    integerJacobian i 37 = tableIntegerJacobian i 37 := by
  unfold integerJacobian
  rw [column_expansion_37, table_column_values_37]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_37
#assert_trust kernel column_table_match_37

theorem column_expansion_38 : integerDerivativeColumns 38 = C (1 : ℤ) * X ^ 2 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_38 : ∀ i : Fin 45,
    tableIntegerJacobian i 38 = (if i.val = 2 then (1 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_38 (i : Fin 45) :
    integerJacobian i 38 = tableIntegerJacobian i 38 := by
  unfold integerJacobian
  rw [column_expansion_38, table_column_values_38]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_38
#assert_trust kernel column_table_match_38

theorem column_expansion_39 : integerDerivativeColumns 39 = C (1 : ℤ) * X ^ 3 + C (1 : ℤ) * X ^ 4 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_39 : ∀ i : Fin 45,
    tableIntegerJacobian i 39 = (if i.val = 3 then (1 : ℤ) else 0) + (if i.val = 4 then (1 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_39 (i : Fin 45) :
    integerJacobian i 39 = tableIntegerJacobian i 39 := by
  unfold integerJacobian
  rw [column_expansion_39, table_column_values_39]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_39
#assert_trust kernel column_table_match_39

end Mod3Certificate
end NLA.MF14Degree44
