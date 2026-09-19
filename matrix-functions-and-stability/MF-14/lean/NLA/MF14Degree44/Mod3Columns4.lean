import NLA.MF14Degree44.Mod3Lists

set_option autoImplicit false
open Polynomial
open scoped BigOperators Matrix
noncomputable section
namespace NLA.MF14Degree44
namespace Mod3Certificate

theorem column_expansion_20 : integerDerivativeColumns 20 = C (1 : ℤ) * X ^ 17 + C (1 : ℤ) * X ^ 18 + C (1 : ℤ) * X ^ 20 + C (1 : ℤ) * X ^ 21 + C (1 : ℤ) * X ^ 26 + C (1 : ℤ) * X ^ 29 + C (1 : ℤ) * X ^ 31 + C (2 : ℤ) * X ^ 33 + C (1 : ℤ) * X ^ 34 + C (4 : ℤ) * X ^ 36 + C (2 : ℤ) * X ^ 39 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_20 : ∀ i : Fin 45,
    tableIntegerJacobian i 20 = (if i.val = 17 then (1 : ℤ) else 0) + (if i.val = 18 then (1 : ℤ) else 0) + (if i.val = 20 then (1 : ℤ) else 0) + (if i.val = 21 then (1 : ℤ) else 0) + (if i.val = 26 then (1 : ℤ) else 0) + (if i.val = 29 then (1 : ℤ) else 0) + (if i.val = 31 then (1 : ℤ) else 0) + (if i.val = 33 then (2 : ℤ) else 0) + (if i.val = 34 then (1 : ℤ) else 0) + (if i.val = 36 then (4 : ℤ) else 0) + (if i.val = 39 then (2 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_20 (i : Fin 45) :
    integerJacobian i 20 = tableIntegerJacobian i 20 := by
  unfold integerJacobian
  rw [column_expansion_20, table_column_values_20]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_20
#assert_trust kernel column_table_match_20

theorem column_expansion_21 : integerDerivativeColumns 21 = C (1 : ℤ) * X ^ 21 + C (1 : ℤ) * X ^ 22 + C (1 : ℤ) * X ^ 30 + C (1 : ℤ) * X ^ 35 + C (2 : ℤ) * X ^ 37 + C (2 : ℤ) * X ^ 40 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_21 : ∀ i : Fin 45,
    tableIntegerJacobian i 21 = (if i.val = 21 then (1 : ℤ) else 0) + (if i.val = 22 then (1 : ℤ) else 0) + (if i.val = 30 then (1 : ℤ) else 0) + (if i.val = 35 then (1 : ℤ) else 0) + (if i.val = 37 then (2 : ℤ) else 0) + (if i.val = 40 then (2 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_21 (i : Fin 45) :
    integerJacobian i 21 = tableIntegerJacobian i 21 := by
  unfold integerJacobian
  rw [column_expansion_21, table_column_values_21]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_21
#assert_trust kernel column_table_match_21

theorem column_expansion_22 : integerDerivativeColumns 22 = C (1 : ℤ) * X ^ 22 + C (1 : ℤ) * X ^ 23 + C (1 : ℤ) * X ^ 31 + C (1 : ℤ) * X ^ 36 + C (2 : ℤ) * X ^ 38 + C (2 : ℤ) * X ^ 41 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_22 : ∀ i : Fin 45,
    tableIntegerJacobian i 22 = (if i.val = 22 then (1 : ℤ) else 0) + (if i.val = 23 then (1 : ℤ) else 0) + (if i.val = 31 then (1 : ℤ) else 0) + (if i.val = 36 then (1 : ℤ) else 0) + (if i.val = 38 then (2 : ℤ) else 0) + (if i.val = 41 then (2 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_22 (i : Fin 45) :
    integerJacobian i 22 = tableIntegerJacobian i 22 := by
  unfold integerJacobian
  rw [column_expansion_22, table_column_values_22]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_22
#assert_trust kernel column_table_match_22

theorem column_expansion_23 : integerDerivativeColumns 23 = C (1 : ℤ) * X ^ 23 + C (2 : ℤ) * X ^ 24 + C (1 : ℤ) * X ^ 25 + C (1 : ℤ) * X ^ 32 + C (1 : ℤ) * X ^ 33 + C (1 : ℤ) * X ^ 37 + C (1 : ℤ) * X ^ 38 + C (2 : ℤ) * X ^ 39 + C (2 : ℤ) * X ^ 40 + C (2 : ℤ) * X ^ 42 + C (2 : ℤ) * X ^ 43 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_23 : ∀ i : Fin 45,
    tableIntegerJacobian i 23 = (if i.val = 23 then (1 : ℤ) else 0) + (if i.val = 24 then (2 : ℤ) else 0) + (if i.val = 25 then (1 : ℤ) else 0) + (if i.val = 32 then (1 : ℤ) else 0) + (if i.val = 33 then (1 : ℤ) else 0) + (if i.val = 37 then (1 : ℤ) else 0) + (if i.val = 38 then (1 : ℤ) else 0) + (if i.val = 39 then (2 : ℤ) else 0) + (if i.val = 40 then (2 : ℤ) else 0) + (if i.val = 42 then (2 : ℤ) else 0) + (if i.val = 43 then (2 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_23 (i : Fin 45) :
    integerJacobian i 23 = tableIntegerJacobian i 23 := by
  unfold integerJacobian
  rw [column_expansion_23, table_column_values_23]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_23
#assert_trust kernel column_table_match_23

theorem column_expansion_24 : integerDerivativeColumns 24 = C (1 : ℤ) * X ^ 4 + C (1 : ℤ) * X ^ 5 + C (1 : ℤ) * X ^ 13 + C (1 : ℤ) * X ^ 18 + C (1 : ℤ) * X ^ 20 + C (1 : ℤ) * X ^ 23 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_24 : ∀ i : Fin 45,
    tableIntegerJacobian i 24 = (if i.val = 4 then (1 : ℤ) else 0) + (if i.val = 5 then (1 : ℤ) else 0) + (if i.val = 13 then (1 : ℤ) else 0) + (if i.val = 18 then (1 : ℤ) else 0) + (if i.val = 20 then (1 : ℤ) else 0) + (if i.val = 23 then (1 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_24 (i : Fin 45) :
    integerJacobian i 24 = tableIntegerJacobian i 24 := by
  unfold integerJacobian
  rw [column_expansion_24, table_column_values_24]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_24
#assert_trust kernel column_table_match_24

end Mod3Certificate
end NLA.MF14Degree44
