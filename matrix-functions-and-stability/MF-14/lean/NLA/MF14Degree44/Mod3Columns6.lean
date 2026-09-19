import NLA.MF14Degree44.Mod3Lists

set_option autoImplicit false
open Polynomial
open scoped BigOperators Matrix
noncomputable section
namespace NLA.MF14Degree44
namespace Mod3Certificate

theorem column_expansion_30 : integerDerivativeColumns 30 = C (1 : ℤ) * X ^ 20 + C (1 : ℤ) * X ^ 23 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_30 : ∀ i : Fin 45,
    tableIntegerJacobian i 30 = (if i.val = 20 then (1 : ℤ) else 0) + (if i.val = 23 then (1 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_30 (i : Fin 45) :
    integerJacobian i 30 = tableIntegerJacobian i 30 := by
  unfold integerJacobian
  rw [column_expansion_30, table_column_values_30]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_30
#assert_trust kernel column_table_match_30

theorem column_expansion_31 : integerDerivativeColumns 31 = C (1 : ℤ) * X ^ 21 + C (1 : ℤ) * X ^ 24 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_31 : ∀ i : Fin 45,
    tableIntegerJacobian i 31 = (if i.val = 21 then (1 : ℤ) else 0) + (if i.val = 24 then (1 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_31 (i : Fin 45) :
    integerJacobian i 31 = tableIntegerJacobian i 31 := by
  unfold integerJacobian
  rw [column_expansion_31, table_column_values_31]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_31
#assert_trust kernel column_table_match_31

theorem column_expansion_32 : integerDerivativeColumns 32 = C (1 : ℤ) * X ^ 22 + C (1 : ℤ) * X ^ 23 + C (1 : ℤ) * X ^ 25 + C (1 : ℤ) * X ^ 26 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_32 : ∀ i : Fin 45,
    tableIntegerJacobian i 32 = (if i.val = 22 then (1 : ℤ) else 0) + (if i.val = 23 then (1 : ℤ) else 0) + (if i.val = 25 then (1 : ℤ) else 0) + (if i.val = 26 then (1 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_32 (i : Fin 45) :
    integerJacobian i 32 = tableIntegerJacobian i 32 := by
  unfold integerJacobian
  rw [column_expansion_32, table_column_values_32]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_32
#assert_trust kernel column_table_match_32

theorem column_expansion_33 : integerDerivativeColumns 33 = C (1 : ℤ) * X ^ 24 + C (1 : ℤ) * X ^ 27 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_33 : ∀ i : Fin 45,
    tableIntegerJacobian i 33 = (if i.val = 24 then (1 : ℤ) else 0) + (if i.val = 27 then (1 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_33 (i : Fin 45) :
    integerJacobian i 33 = tableIntegerJacobian i 33 := by
  unfold integerJacobian
  rw [column_expansion_33, table_column_values_33]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_33
#assert_trust kernel column_table_match_33

theorem column_expansion_34 : integerDerivativeColumns 34 = C (1 : ℤ) * X ^ 31 + C (1 : ℤ) * X ^ 34 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_34 : ∀ i : Fin 45,
    tableIntegerJacobian i 34 = (if i.val = 31 then (1 : ℤ) else 0) + (if i.val = 34 then (1 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_34 (i : Fin 45) :
    integerJacobian i 34 = tableIntegerJacobian i 34 := by
  unfold integerJacobian
  rw [column_expansion_34, table_column_values_34]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_34
#assert_trust kernel column_table_match_34

end Mod3Certificate
end NLA.MF14Degree44
