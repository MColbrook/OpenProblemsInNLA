import NLA.MF14Degree44.Mod3Lists

set_option autoImplicit false
open Polynomial
open scoped BigOperators Matrix
noncomputable section
namespace NLA.MF14Degree44
namespace Mod3Certificate

theorem column_expansion_15 : integerDerivativeColumns 15 = C (1 : ℤ) * X ^ 20 + C (2 : ℤ) * X ^ 21 + C (1 : ℤ) * X ^ 22 + C (1 : ℤ) * X ^ 23 + C (2 : ℤ) * X ^ 24 + C (1 : ℤ) * X ^ 25 + C (1 : ℤ) * X ^ 29 + C (1 : ℤ) * X ^ 30 + C (1 : ℤ) * X ^ 32 + C (1 : ℤ) * X ^ 33 + C (2 : ℤ) * X ^ 34 + C (2 : ℤ) * X ^ 35 + C (2 : ℤ) * X ^ 36 + C (4 : ℤ) * X ^ 37 + C (2 : ℤ) * X ^ 38 + C (4 : ℤ) * X ^ 39 + C (4 : ℤ) * X ^ 40 + C (2 : ℤ) * X ^ 42 + C (2 : ℤ) * X ^ 43 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_15 : ∀ i : Fin 45,
    tableIntegerJacobian i 15 = (if i.val = 20 then (1 : ℤ) else 0) + (if i.val = 21 then (2 : ℤ) else 0) + (if i.val = 22 then (1 : ℤ) else 0) + (if i.val = 23 then (1 : ℤ) else 0) + (if i.val = 24 then (2 : ℤ) else 0) + (if i.val = 25 then (1 : ℤ) else 0) + (if i.val = 29 then (1 : ℤ) else 0) + (if i.val = 30 then (1 : ℤ) else 0) + (if i.val = 32 then (1 : ℤ) else 0) + (if i.val = 33 then (1 : ℤ) else 0) + (if i.val = 34 then (2 : ℤ) else 0) + (if i.val = 35 then (2 : ℤ) else 0) + (if i.val = 36 then (2 : ℤ) else 0) + (if i.val = 37 then (4 : ℤ) else 0) + (if i.val = 38 then (2 : ℤ) else 0) + (if i.val = 39 then (4 : ℤ) else 0) + (if i.val = 40 then (4 : ℤ) else 0) + (if i.val = 42 then (2 : ℤ) else 0) + (if i.val = 43 then (2 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_15 (i : Fin 45) :
    integerJacobian i 15 = tableIntegerJacobian i 15 := by
  unfold integerJacobian
  rw [column_expansion_15, table_column_values_15]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_15
#assert_trust kernel column_table_match_15

theorem column_expansion_16 : integerDerivativeColumns 16 = C (1 : ℤ) * X ^ 6 + C (1 : ℤ) * X ^ 7 + C (1 : ℤ) * X ^ 9 + C (1 : ℤ) * X ^ 10 + C (1 : ℤ) * X ^ 15 + C (1 : ℤ) * X ^ 18 + C (1 : ℤ) * X ^ 20 + C (2 : ℤ) * X ^ 22 + C (1 : ℤ) * X ^ 23 + C (4 : ℤ) * X ^ 25 + C (2 : ℤ) * X ^ 28 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_16 : ∀ i : Fin 45,
    tableIntegerJacobian i 16 = (if i.val = 6 then (1 : ℤ) else 0) + (if i.val = 7 then (1 : ℤ) else 0) + (if i.val = 9 then (1 : ℤ) else 0) + (if i.val = 10 then (1 : ℤ) else 0) + (if i.val = 15 then (1 : ℤ) else 0) + (if i.val = 18 then (1 : ℤ) else 0) + (if i.val = 20 then (1 : ℤ) else 0) + (if i.val = 22 then (2 : ℤ) else 0) + (if i.val = 23 then (1 : ℤ) else 0) + (if i.val = 25 then (4 : ℤ) else 0) + (if i.val = 28 then (2 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_16 (i : Fin 45) :
    integerJacobian i 16 = tableIntegerJacobian i 16 := by
  unfold integerJacobian
  rw [column_expansion_16, table_column_values_16]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_16
#assert_trust kernel column_table_match_16

theorem column_expansion_17 : integerDerivativeColumns 17 = C (1 : ℤ) * X ^ 7 + C (1 : ℤ) * X ^ 8 + C (1 : ℤ) * X ^ 10 + C (1 : ℤ) * X ^ 11 + C (1 : ℤ) * X ^ 16 + C (1 : ℤ) * X ^ 19 + C (1 : ℤ) * X ^ 21 + C (2 : ℤ) * X ^ 23 + C (1 : ℤ) * X ^ 24 + C (4 : ℤ) * X ^ 26 + C (2 : ℤ) * X ^ 29 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_17 : ∀ i : Fin 45,
    tableIntegerJacobian i 17 = (if i.val = 7 then (1 : ℤ) else 0) + (if i.val = 8 then (1 : ℤ) else 0) + (if i.val = 10 then (1 : ℤ) else 0) + (if i.val = 11 then (1 : ℤ) else 0) + (if i.val = 16 then (1 : ℤ) else 0) + (if i.val = 19 then (1 : ℤ) else 0) + (if i.val = 21 then (1 : ℤ) else 0) + (if i.val = 23 then (2 : ℤ) else 0) + (if i.val = 24 then (1 : ℤ) else 0) + (if i.val = 26 then (4 : ℤ) else 0) + (if i.val = 29 then (2 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_17 (i : Fin 45) :
    integerJacobian i 17 = tableIntegerJacobian i 17 := by
  unfold integerJacobian
  rw [column_expansion_17, table_column_values_17]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_17
#assert_trust kernel column_table_match_17

theorem column_expansion_18 : integerDerivativeColumns 18 = C (1 : ℤ) * X ^ 8 + C (2 : ℤ) * X ^ 9 + C (1 : ℤ) * X ^ 10 + C (1 : ℤ) * X ^ 11 + C (2 : ℤ) * X ^ 12 + C (1 : ℤ) * X ^ 13 + C (1 : ℤ) * X ^ 17 + C (1 : ℤ) * X ^ 18 + C (1 : ℤ) * X ^ 20 + C (1 : ℤ) * X ^ 21 + C (1 : ℤ) * X ^ 22 + C (1 : ℤ) * X ^ 23 + C (2 : ℤ) * X ^ 24 + C (3 : ℤ) * X ^ 25 + C (1 : ℤ) * X ^ 26 + C (4 : ℤ) * X ^ 27 + C (4 : ℤ) * X ^ 28 + C (2 : ℤ) * X ^ 30 + C (2 : ℤ) * X ^ 31 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_18 : ∀ i : Fin 45,
    tableIntegerJacobian i 18 = (if i.val = 8 then (1 : ℤ) else 0) + (if i.val = 9 then (2 : ℤ) else 0) + (if i.val = 10 then (1 : ℤ) else 0) + (if i.val = 11 then (1 : ℤ) else 0) + (if i.val = 12 then (2 : ℤ) else 0) + (if i.val = 13 then (1 : ℤ) else 0) + (if i.val = 17 then (1 : ℤ) else 0) + (if i.val = 18 then (1 : ℤ) else 0) + (if i.val = 20 then (1 : ℤ) else 0) + (if i.val = 21 then (1 : ℤ) else 0) + (if i.val = 22 then (1 : ℤ) else 0) + (if i.val = 23 then (1 : ℤ) else 0) + (if i.val = 24 then (2 : ℤ) else 0) + (if i.val = 25 then (3 : ℤ) else 0) + (if i.val = 26 then (1 : ℤ) else 0) + (if i.val = 27 then (4 : ℤ) else 0) + (if i.val = 28 then (4 : ℤ) else 0) + (if i.val = 30 then (2 : ℤ) else 0) + (if i.val = 31 then (2 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_18 (i : Fin 45) :
    integerJacobian i 18 = tableIntegerJacobian i 18 := by
  unfold integerJacobian
  rw [column_expansion_18, table_column_values_18]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_18
#assert_trust kernel column_table_match_18

theorem column_expansion_19 : integerDerivativeColumns 19 = C (1 : ℤ) * X ^ 10 + C (1 : ℤ) * X ^ 11 + C (1 : ℤ) * X ^ 13 + C (1 : ℤ) * X ^ 14 + C (1 : ℤ) * X ^ 19 + C (1 : ℤ) * X ^ 22 + C (1 : ℤ) * X ^ 24 + C (2 : ℤ) * X ^ 26 + C (1 : ℤ) * X ^ 27 + C (4 : ℤ) * X ^ 29 + C (2 : ℤ) * X ^ 32 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_19 : ∀ i : Fin 45,
    tableIntegerJacobian i 19 = (if i.val = 10 then (1 : ℤ) else 0) + (if i.val = 11 then (1 : ℤ) else 0) + (if i.val = 13 then (1 : ℤ) else 0) + (if i.val = 14 then (1 : ℤ) else 0) + (if i.val = 19 then (1 : ℤ) else 0) + (if i.val = 22 then (1 : ℤ) else 0) + (if i.val = 24 then (1 : ℤ) else 0) + (if i.val = 26 then (2 : ℤ) else 0) + (if i.val = 27 then (1 : ℤ) else 0) + (if i.val = 29 then (4 : ℤ) else 0) + (if i.val = 32 then (2 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_19 (i : Fin 45) :
    integerJacobian i 19 = tableIntegerJacobian i 19 := by
  unfold integerJacobian
  rw [column_expansion_19, table_column_values_19]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_19
#assert_trust kernel column_table_match_19

end Mod3Certificate
end NLA.MF14Degree44
