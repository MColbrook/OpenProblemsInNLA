import NLA.MF14Degree44.Mod3Lists

set_option autoImplicit false
open Polynomial
open scoped BigOperators Matrix
noncomputable section
namespace NLA.MF14Degree44
namespace Mod3Certificate

theorem column_expansion_10 : integerDerivativeColumns 10 = C (1 : ℤ) * X ^ 12 + C (1 : ℤ) * X ^ 13 + C (1 : ℤ) * X ^ 15 + C (1 : ℤ) * X ^ 16 + C (1 : ℤ) * X ^ 21 + C (1 : ℤ) * X ^ 24 + C (2 : ℤ) * X ^ 26 + C (2 : ℤ) * X ^ 28 + C (2 : ℤ) * X ^ 29 + C (4 : ℤ) * X ^ 31 + C (2 : ℤ) * X ^ 34 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_10 : ∀ i : Fin 45,
    tableIntegerJacobian i 10 = (if i.val = 12 then (1 : ℤ) else 0) + (if i.val = 13 then (1 : ℤ) else 0) + (if i.val = 15 then (1 : ℤ) else 0) + (if i.val = 16 then (1 : ℤ) else 0) + (if i.val = 21 then (1 : ℤ) else 0) + (if i.val = 24 then (1 : ℤ) else 0) + (if i.val = 26 then (2 : ℤ) else 0) + (if i.val = 28 then (2 : ℤ) else 0) + (if i.val = 29 then (2 : ℤ) else 0) + (if i.val = 31 then (4 : ℤ) else 0) + (if i.val = 34 then (2 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_10 (i : Fin 45) :
    integerJacobian i 10 = tableIntegerJacobian i 10 := by
  unfold integerJacobian
  rw [column_expansion_10, table_column_values_10]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_10
#assert_trust kernel column_table_match_10

theorem column_expansion_11 : integerDerivativeColumns 11 = C (1 : ℤ) * X ^ 13 + C (2 : ℤ) * X ^ 14 + C (1 : ℤ) * X ^ 15 + C (1 : ℤ) * X ^ 16 + C (2 : ℤ) * X ^ 17 + C (1 : ℤ) * X ^ 18 + C (1 : ℤ) * X ^ 22 + C (1 : ℤ) * X ^ 23 + C (1 : ℤ) * X ^ 25 + C (1 : ℤ) * X ^ 26 + C (2 : ℤ) * X ^ 27 + C (2 : ℤ) * X ^ 28 + C (2 : ℤ) * X ^ 29 + C (4 : ℤ) * X ^ 30 + C (2 : ℤ) * X ^ 31 + C (4 : ℤ) * X ^ 32 + C (4 : ℤ) * X ^ 33 + C (2 : ℤ) * X ^ 35 + C (2 : ℤ) * X ^ 36 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_11 : ∀ i : Fin 45,
    tableIntegerJacobian i 11 = (if i.val = 13 then (1 : ℤ) else 0) + (if i.val = 14 then (2 : ℤ) else 0) + (if i.val = 15 then (1 : ℤ) else 0) + (if i.val = 16 then (1 : ℤ) else 0) + (if i.val = 17 then (2 : ℤ) else 0) + (if i.val = 18 then (1 : ℤ) else 0) + (if i.val = 22 then (1 : ℤ) else 0) + (if i.val = 23 then (1 : ℤ) else 0) + (if i.val = 25 then (1 : ℤ) else 0) + (if i.val = 26 then (1 : ℤ) else 0) + (if i.val = 27 then (2 : ℤ) else 0) + (if i.val = 28 then (2 : ℤ) else 0) + (if i.val = 29 then (2 : ℤ) else 0) + (if i.val = 30 then (4 : ℤ) else 0) + (if i.val = 31 then (2 : ℤ) else 0) + (if i.val = 32 then (4 : ℤ) else 0) + (if i.val = 33 then (4 : ℤ) else 0) + (if i.val = 35 then (2 : ℤ) else 0) + (if i.val = 36 then (2 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_11 (i : Fin 45) :
    integerJacobian i 11 = tableIntegerJacobian i 11 := by
  unfold integerJacobian
  rw [column_expansion_11, table_column_values_11]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_11
#assert_trust kernel column_table_match_11

theorem column_expansion_12 : integerDerivativeColumns 12 = C (1 : ℤ) * X ^ 15 + C (1 : ℤ) * X ^ 16 + C (1 : ℤ) * X ^ 18 + C (1 : ℤ) * X ^ 19 + C (1 : ℤ) * X ^ 24 + C (1 : ℤ) * X ^ 27 + C (2 : ℤ) * X ^ 29 + C (2 : ℤ) * X ^ 31 + C (2 : ℤ) * X ^ 32 + C (4 : ℤ) * X ^ 34 + C (2 : ℤ) * X ^ 37 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_12 : ∀ i : Fin 45,
    tableIntegerJacobian i 12 = (if i.val = 15 then (1 : ℤ) else 0) + (if i.val = 16 then (1 : ℤ) else 0) + (if i.val = 18 then (1 : ℤ) else 0) + (if i.val = 19 then (1 : ℤ) else 0) + (if i.val = 24 then (1 : ℤ) else 0) + (if i.val = 27 then (1 : ℤ) else 0) + (if i.val = 29 then (2 : ℤ) else 0) + (if i.val = 31 then (2 : ℤ) else 0) + (if i.val = 32 then (2 : ℤ) else 0) + (if i.val = 34 then (4 : ℤ) else 0) + (if i.val = 37 then (2 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_12 (i : Fin 45) :
    integerJacobian i 12 = tableIntegerJacobian i 12 := by
  unfold integerJacobian
  rw [column_expansion_12, table_column_values_12]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_12
#assert_trust kernel column_table_match_12

theorem column_expansion_13 : integerDerivativeColumns 13 = C (1 : ℤ) * X ^ 18 + C (1 : ℤ) * X ^ 19 + C (1 : ℤ) * X ^ 21 + C (1 : ℤ) * X ^ 22 + C (1 : ℤ) * X ^ 27 + C (1 : ℤ) * X ^ 30 + C (2 : ℤ) * X ^ 32 + C (2 : ℤ) * X ^ 34 + C (2 : ℤ) * X ^ 35 + C (4 : ℤ) * X ^ 37 + C (2 : ℤ) * X ^ 40 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_13 : ∀ i : Fin 45,
    tableIntegerJacobian i 13 = (if i.val = 18 then (1 : ℤ) else 0) + (if i.val = 19 then (1 : ℤ) else 0) + (if i.val = 21 then (1 : ℤ) else 0) + (if i.val = 22 then (1 : ℤ) else 0) + (if i.val = 27 then (1 : ℤ) else 0) + (if i.val = 30 then (1 : ℤ) else 0) + (if i.val = 32 then (2 : ℤ) else 0) + (if i.val = 34 then (2 : ℤ) else 0) + (if i.val = 35 then (2 : ℤ) else 0) + (if i.val = 37 then (4 : ℤ) else 0) + (if i.val = 40 then (2 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_13 (i : Fin 45) :
    integerJacobian i 13 = tableIntegerJacobian i 13 := by
  unfold integerJacobian
  rw [column_expansion_13, table_column_values_13]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_13
#assert_trust kernel column_table_match_13

theorem column_expansion_14 : integerDerivativeColumns 14 = C (1 : ℤ) * X ^ 19 + C (1 : ℤ) * X ^ 20 + C (1 : ℤ) * X ^ 22 + C (1 : ℤ) * X ^ 23 + C (1 : ℤ) * X ^ 28 + C (1 : ℤ) * X ^ 31 + C (2 : ℤ) * X ^ 33 + C (2 : ℤ) * X ^ 35 + C (2 : ℤ) * X ^ 36 + C (4 : ℤ) * X ^ 38 + C (2 : ℤ) * X ^ 41 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_14 : ∀ i : Fin 45,
    tableIntegerJacobian i 14 = (if i.val = 19 then (1 : ℤ) else 0) + (if i.val = 20 then (1 : ℤ) else 0) + (if i.val = 22 then (1 : ℤ) else 0) + (if i.val = 23 then (1 : ℤ) else 0) + (if i.val = 28 then (1 : ℤ) else 0) + (if i.val = 31 then (1 : ℤ) else 0) + (if i.val = 33 then (2 : ℤ) else 0) + (if i.val = 35 then (2 : ℤ) else 0) + (if i.val = 36 then (2 : ℤ) else 0) + (if i.val = 38 then (4 : ℤ) else 0) + (if i.val = 41 then (2 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_14 (i : Fin 45) :
    integerJacobian i 14 = tableIntegerJacobian i 14 := by
  unfold integerJacobian
  rw [column_expansion_14, table_column_values_14]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_14
#assert_trust kernel column_table_match_14

end Mod3Certificate
end NLA.MF14Degree44
