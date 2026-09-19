import NLA.MF14Degree44.Mod3Lists

set_option autoImplicit false
open Polynomial
open scoped BigOperators Matrix
noncomputable section
namespace NLA.MF14Degree44
namespace Mod3Certificate

theorem column_expansion_0 : integerDerivativeColumns 0 = C (1 : ℤ) * X ^ 22 + C (1 : ℤ) * X ^ 25 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_0 : ∀ i : Fin 45,
    tableIntegerJacobian i 0 = (if i.val = 22 then (1 : ℤ) else 0) + (if i.val = 25 then (1 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_0 (i : Fin 45) :
    integerJacobian i 0 = tableIntegerJacobian i 0 := by
  unfold integerJacobian
  rw [column_expansion_0, table_column_values_0]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_0
#assert_trust kernel column_table_match_0

theorem column_expansion_1 : integerDerivativeColumns 1 = C (1 : ℤ) * X ^ 20 + C (1 : ℤ) * X ^ 21 + C (2 : ℤ) * X ^ 23 + C (2 : ℤ) * X ^ 24 + C (1 : ℤ) * X ^ 29 + C (2 : ℤ) * X ^ 32 + C (2 : ℤ) * X ^ 34 + C (2 : ℤ) * X ^ 36 + C (3 : ℤ) * X ^ 37 + C (6 : ℤ) * X ^ 39 + C (4 : ℤ) * X ^ 42 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_1 : ∀ i : Fin 45,
    tableIntegerJacobian i 1 = (if i.val = 20 then (1 : ℤ) else 0) + (if i.val = 21 then (1 : ℤ) else 0) + (if i.val = 23 then (2 : ℤ) else 0) + (if i.val = 24 then (2 : ℤ) else 0) + (if i.val = 29 then (1 : ℤ) else 0) + (if i.val = 32 then (2 : ℤ) else 0) + (if i.val = 34 then (2 : ℤ) else 0) + (if i.val = 36 then (2 : ℤ) else 0) + (if i.val = 37 then (3 : ℤ) else 0) + (if i.val = 39 then (6 : ℤ) else 0) + (if i.val = 42 then (4 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_1 (i : Fin 45) :
    integerJacobian i 1 = tableIntegerJacobian i 1 := by
  unfold integerJacobian
  rw [column_expansion_1, table_column_values_1]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_1
#assert_trust kernel column_table_match_1

theorem column_expansion_2 : integerDerivativeColumns 2 = C (1 : ℤ) * X ^ 13 + C (1 : ℤ) * X ^ 14 + C (1 : ℤ) * X ^ 16 + C (1 : ℤ) * X ^ 17 + C (2 : ℤ) * X ^ 22 + C (2 : ℤ) * X ^ 25 + C (2 : ℤ) * X ^ 27 + C (2 : ℤ) * X ^ 29 + C (2 : ℤ) * X ^ 30 + C (4 : ℤ) * X ^ 32 + C (2 : ℤ) * X ^ 35 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_2 : ∀ i : Fin 45,
    tableIntegerJacobian i 2 = (if i.val = 13 then (1 : ℤ) else 0) + (if i.val = 14 then (1 : ℤ) else 0) + (if i.val = 16 then (1 : ℤ) else 0) + (if i.val = 17 then (1 : ℤ) else 0) + (if i.val = 22 then (2 : ℤ) else 0) + (if i.val = 25 then (2 : ℤ) else 0) + (if i.val = 27 then (2 : ℤ) else 0) + (if i.val = 29 then (2 : ℤ) else 0) + (if i.val = 30 then (2 : ℤ) else 0) + (if i.val = 32 then (4 : ℤ) else 0) + (if i.val = 35 then (2 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_2 (i : Fin 45) :
    integerJacobian i 2 = tableIntegerJacobian i 2 := by
  unfold integerJacobian
  rw [column_expansion_2, table_column_values_2]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_2
#assert_trust kernel column_table_match_2

theorem column_expansion_3 : integerDerivativeColumns 3 = C (1 : ℤ) * X ^ 16 + C (1 : ℤ) * X ^ 17 + C (1 : ℤ) * X ^ 19 + C (1 : ℤ) * X ^ 20 + C (2 : ℤ) * X ^ 25 + C (2 : ℤ) * X ^ 28 + C (2 : ℤ) * X ^ 30 + C (2 : ℤ) * X ^ 32 + C (2 : ℤ) * X ^ 33 + C (4 : ℤ) * X ^ 35 + C (2 : ℤ) * X ^ 38 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_3 : ∀ i : Fin 45,
    tableIntegerJacobian i 3 = (if i.val = 16 then (1 : ℤ) else 0) + (if i.val = 17 then (1 : ℤ) else 0) + (if i.val = 19 then (1 : ℤ) else 0) + (if i.val = 20 then (1 : ℤ) else 0) + (if i.val = 25 then (2 : ℤ) else 0) + (if i.val = 28 then (2 : ℤ) else 0) + (if i.val = 30 then (2 : ℤ) else 0) + (if i.val = 32 then (2 : ℤ) else 0) + (if i.val = 33 then (2 : ℤ) else 0) + (if i.val = 35 then (4 : ℤ) else 0) + (if i.val = 38 then (2 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_3 (i : Fin 45) :
    integerJacobian i 3 = tableIntegerJacobian i 3 := by
  unfold integerJacobian
  rw [column_expansion_3, table_column_values_3]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_3
#assert_trust kernel column_table_match_3

theorem column_expansion_4 : integerDerivativeColumns 4 = C (1 : ℤ) * X ^ 17 + C (1 : ℤ) * X ^ 18 + C (1 : ℤ) * X ^ 20 + C (1 : ℤ) * X ^ 21 + C (2 : ℤ) * X ^ 26 + C (2 : ℤ) * X ^ 29 + C (2 : ℤ) * X ^ 31 + C (2 : ℤ) * X ^ 33 + C (2 : ℤ) * X ^ 34 + C (4 : ℤ) * X ^ 36 + C (2 : ℤ) * X ^ 39 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_4 : ∀ i : Fin 45,
    tableIntegerJacobian i 4 = (if i.val = 17 then (1 : ℤ) else 0) + (if i.val = 18 then (1 : ℤ) else 0) + (if i.val = 20 then (1 : ℤ) else 0) + (if i.val = 21 then (1 : ℤ) else 0) + (if i.val = 26 then (2 : ℤ) else 0) + (if i.val = 29 then (2 : ℤ) else 0) + (if i.val = 31 then (2 : ℤ) else 0) + (if i.val = 33 then (2 : ℤ) else 0) + (if i.val = 34 then (2 : ℤ) else 0) + (if i.val = 36 then (4 : ℤ) else 0) + (if i.val = 39 then (2 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_4 (i : Fin 45) :
    integerJacobian i 4 = tableIntegerJacobian i 4 := by
  unfold integerJacobian
  rw [column_expansion_4, table_column_values_4]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_4
#assert_trust kernel column_table_match_4

end Mod3Certificate
end NLA.MF14Degree44
