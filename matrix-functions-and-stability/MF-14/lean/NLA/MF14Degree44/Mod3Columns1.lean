import NLA.MF14Degree44.Mod3Lists

set_option autoImplicit false
open Polynomial
open scoped BigOperators Matrix
noncomputable section
namespace NLA.MF14Degree44
namespace Mod3Certificate

theorem column_expansion_5 : integerDerivativeColumns 5 = C (1 : ℤ) * X ^ 18 + C (1 : ℤ) * X ^ 19 + C (1 : ℤ) * X ^ 21 + C (1 : ℤ) * X ^ 22 + C (2 : ℤ) * X ^ 27 + C (2 : ℤ) * X ^ 30 + C (2 : ℤ) * X ^ 32 + C (2 : ℤ) * X ^ 34 + C (2 : ℤ) * X ^ 35 + C (4 : ℤ) * X ^ 37 + C (2 : ℤ) * X ^ 40 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_5 : ∀ i : Fin 45,
    tableIntegerJacobian i 5 = (if i.val = 18 then (1 : ℤ) else 0) + (if i.val = 19 then (1 : ℤ) else 0) + (if i.val = 21 then (1 : ℤ) else 0) + (if i.val = 22 then (1 : ℤ) else 0) + (if i.val = 27 then (2 : ℤ) else 0) + (if i.val = 30 then (2 : ℤ) else 0) + (if i.val = 32 then (2 : ℤ) else 0) + (if i.val = 34 then (2 : ℤ) else 0) + (if i.val = 35 then (2 : ℤ) else 0) + (if i.val = 37 then (4 : ℤ) else 0) + (if i.val = 40 then (2 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_5 (i : Fin 45) :
    integerJacobian i 5 = tableIntegerJacobian i 5 := by
  unfold integerJacobian
  rw [column_expansion_5, table_column_values_5]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_5
#assert_trust kernel column_table_match_5

theorem column_expansion_6 : integerDerivativeColumns 6 = C (1 : ℤ) * X ^ 19 + C (1 : ℤ) * X ^ 20 + C (1 : ℤ) * X ^ 22 + C (1 : ℤ) * X ^ 23 + C (2 : ℤ) * X ^ 28 + C (2 : ℤ) * X ^ 31 + C (2 : ℤ) * X ^ 33 + C (2 : ℤ) * X ^ 35 + C (2 : ℤ) * X ^ 36 + C (4 : ℤ) * X ^ 38 + C (2 : ℤ) * X ^ 41 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_6 : ∀ i : Fin 45,
    tableIntegerJacobian i 6 = (if i.val = 19 then (1 : ℤ) else 0) + (if i.val = 20 then (1 : ℤ) else 0) + (if i.val = 22 then (1 : ℤ) else 0) + (if i.val = 23 then (1 : ℤ) else 0) + (if i.val = 28 then (2 : ℤ) else 0) + (if i.val = 31 then (2 : ℤ) else 0) + (if i.val = 33 then (2 : ℤ) else 0) + (if i.val = 35 then (2 : ℤ) else 0) + (if i.val = 36 then (2 : ℤ) else 0) + (if i.val = 38 then (4 : ℤ) else 0) + (if i.val = 41 then (2 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_6 (i : Fin 45) :
    integerJacobian i 6 = tableIntegerJacobian i 6 := by
  unfold integerJacobian
  rw [column_expansion_6, table_column_values_6]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_6
#assert_trust kernel column_table_match_6

theorem column_expansion_7 : integerDerivativeColumns 7 = C (1 : ℤ) * X ^ 20 + C (1 : ℤ) * X ^ 21 + C (1 : ℤ) * X ^ 23 + C (1 : ℤ) * X ^ 24 + C (2 : ℤ) * X ^ 29 + C (2 : ℤ) * X ^ 32 + C (2 : ℤ) * X ^ 34 + C (2 : ℤ) * X ^ 36 + C (2 : ℤ) * X ^ 37 + C (4 : ℤ) * X ^ 39 + C (2 : ℤ) * X ^ 42 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_7 : ∀ i : Fin 45,
    tableIntegerJacobian i 7 = (if i.val = 20 then (1 : ℤ) else 0) + (if i.val = 21 then (1 : ℤ) else 0) + (if i.val = 23 then (1 : ℤ) else 0) + (if i.val = 24 then (1 : ℤ) else 0) + (if i.val = 29 then (2 : ℤ) else 0) + (if i.val = 32 then (2 : ℤ) else 0) + (if i.val = 34 then (2 : ℤ) else 0) + (if i.val = 36 then (2 : ℤ) else 0) + (if i.val = 37 then (2 : ℤ) else 0) + (if i.val = 39 then (4 : ℤ) else 0) + (if i.val = 42 then (2 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_7 (i : Fin 45) :
    integerJacobian i 7 = tableIntegerJacobian i 7 := by
  unfold integerJacobian
  rw [column_expansion_7, table_column_values_7]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_7
#assert_trust kernel column_table_match_7

theorem column_expansion_8 : integerDerivativeColumns 8 = C (1 : ℤ) * X ^ 21 + C (1 : ℤ) * X ^ 22 + C (1 : ℤ) * X ^ 24 + C (1 : ℤ) * X ^ 25 + C (2 : ℤ) * X ^ 30 + C (2 : ℤ) * X ^ 33 + C (2 : ℤ) * X ^ 35 + C (2 : ℤ) * X ^ 37 + C (2 : ℤ) * X ^ 38 + C (4 : ℤ) * X ^ 40 + C (2 : ℤ) * X ^ 43 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_8 : ∀ i : Fin 45,
    tableIntegerJacobian i 8 = (if i.val = 21 then (1 : ℤ) else 0) + (if i.val = 22 then (1 : ℤ) else 0) + (if i.val = 24 then (1 : ℤ) else 0) + (if i.val = 25 then (1 : ℤ) else 0) + (if i.val = 30 then (2 : ℤ) else 0) + (if i.val = 33 then (2 : ℤ) else 0) + (if i.val = 35 then (2 : ℤ) else 0) + (if i.val = 37 then (2 : ℤ) else 0) + (if i.val = 38 then (2 : ℤ) else 0) + (if i.val = 40 then (4 : ℤ) else 0) + (if i.val = 43 then (2 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_8 (i : Fin 45) :
    integerJacobian i 8 = tableIntegerJacobian i 8 := by
  unfold integerJacobian
  rw [column_expansion_8, table_column_values_8]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_8
#assert_trust kernel column_table_match_8

theorem column_expansion_9 : integerDerivativeColumns 9 = C (1 : ℤ) * X ^ 11 + C (1 : ℤ) * X ^ 12 + C (1 : ℤ) * X ^ 14 + C (1 : ℤ) * X ^ 15 + C (1 : ℤ) * X ^ 20 + C (1 : ℤ) * X ^ 23 + C (2 : ℤ) * X ^ 25 + C (2 : ℤ) * X ^ 27 + C (2 : ℤ) * X ^ 28 + C (4 : ℤ) * X ^ 30 + C (2 : ℤ) * X ^ 33 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_9 : ∀ i : Fin 45,
    tableIntegerJacobian i 9 = (if i.val = 11 then (1 : ℤ) else 0) + (if i.val = 12 then (1 : ℤ) else 0) + (if i.val = 14 then (1 : ℤ) else 0) + (if i.val = 15 then (1 : ℤ) else 0) + (if i.val = 20 then (1 : ℤ) else 0) + (if i.val = 23 then (1 : ℤ) else 0) + (if i.val = 25 then (2 : ℤ) else 0) + (if i.val = 27 then (2 : ℤ) else 0) + (if i.val = 28 then (2 : ℤ) else 0) + (if i.val = 30 then (4 : ℤ) else 0) + (if i.val = 33 then (2 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_9 (i : Fin 45) :
    integerJacobian i 9 = tableIntegerJacobian i 9 := by
  unfold integerJacobian
  rw [column_expansion_9, table_column_values_9]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_9
#assert_trust kernel column_table_match_9

end Mod3Certificate
end NLA.MF14Degree44
