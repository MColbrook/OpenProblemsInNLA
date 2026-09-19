import NLA.MF14Degree44.Mod3Lists

set_option autoImplicit false
open Polynomial
open scoped BigOperators Matrix
noncomputable section
namespace NLA.MF14Degree44
namespace Mod3Certificate

theorem column_expansion_25 : integerDerivativeColumns 25 = C (1 : ℤ) * X ^ 5 + C (1 : ℤ) * X ^ 6 + C (1 : ℤ) * X ^ 14 + C (1 : ℤ) * X ^ 19 + C (1 : ℤ) * X ^ 21 + C (1 : ℤ) * X ^ 24 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_25 : ∀ i : Fin 45,
    tableIntegerJacobian i 25 = (if i.val = 5 then (1 : ℤ) else 0) + (if i.val = 6 then (1 : ℤ) else 0) + (if i.val = 14 then (1 : ℤ) else 0) + (if i.val = 19 then (1 : ℤ) else 0) + (if i.val = 21 then (1 : ℤ) else 0) + (if i.val = 24 then (1 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_25 (i : Fin 45) :
    integerJacobian i 25 = tableIntegerJacobian i 25 := by
  unfold integerJacobian
  rw [column_expansion_25, table_column_values_25]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_25
#assert_trust kernel column_table_match_25

theorem column_expansion_26 : integerDerivativeColumns 26 = C (1 : ℤ) * X ^ 6 + C (2 : ℤ) * X ^ 7 + C (1 : ℤ) * X ^ 8 + C (1 : ℤ) * X ^ 15 + C (1 : ℤ) * X ^ 16 + C (1 : ℤ) * X ^ 20 + C (1 : ℤ) * X ^ 21 + C (1 : ℤ) * X ^ 22 + C (1 : ℤ) * X ^ 23 + C (1 : ℤ) * X ^ 25 + C (1 : ℤ) * X ^ 26 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_26 : ∀ i : Fin 45,
    tableIntegerJacobian i 26 = (if i.val = 6 then (1 : ℤ) else 0) + (if i.val = 7 then (2 : ℤ) else 0) + (if i.val = 8 then (1 : ℤ) else 0) + (if i.val = 15 then (1 : ℤ) else 0) + (if i.val = 16 then (1 : ℤ) else 0) + (if i.val = 20 then (1 : ℤ) else 0) + (if i.val = 21 then (1 : ℤ) else 0) + (if i.val = 22 then (1 : ℤ) else 0) + (if i.val = 23 then (1 : ℤ) else 0) + (if i.val = 25 then (1 : ℤ) else 0) + (if i.val = 26 then (1 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_26 (i : Fin 45) :
    integerJacobian i 26 = tableIntegerJacobian i 26 := by
  unfold integerJacobian
  rw [column_expansion_26, table_column_values_26]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_26
#assert_trust kernel column_table_match_26

theorem column_expansion_27 : integerDerivativeColumns 27 = C (1 : ℤ) * X ^ 8 + C (1 : ℤ) * X ^ 9 + C (1 : ℤ) * X ^ 17 + C (1 : ℤ) * X ^ 22 + C (1 : ℤ) * X ^ 24 + C (1 : ℤ) * X ^ 27 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_27 : ∀ i : Fin 45,
    tableIntegerJacobian i 27 = (if i.val = 8 then (1 : ℤ) else 0) + (if i.val = 9 then (1 : ℤ) else 0) + (if i.val = 17 then (1 : ℤ) else 0) + (if i.val = 22 then (1 : ℤ) else 0) + (if i.val = 24 then (1 : ℤ) else 0) + (if i.val = 27 then (1 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_27 (i : Fin 45) :
    integerJacobian i 27 = tableIntegerJacobian i 27 := by
  unfold integerJacobian
  rw [column_expansion_27, table_column_values_27]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_27
#assert_trust kernel column_table_match_27

theorem column_expansion_28 : integerDerivativeColumns 28 = C (1 : ℤ) * X ^ 15 + C (1 : ℤ) * X ^ 16 + C (1 : ℤ) * X ^ 24 + C (1 : ℤ) * X ^ 29 + C (1 : ℤ) * X ^ 31 + C (1 : ℤ) * X ^ 34 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_28 : ∀ i : Fin 45,
    tableIntegerJacobian i 28 = (if i.val = 15 then (1 : ℤ) else 0) + (if i.val = 16 then (1 : ℤ) else 0) + (if i.val = 24 then (1 : ℤ) else 0) + (if i.val = 29 then (1 : ℤ) else 0) + (if i.val = 31 then (1 : ℤ) else 0) + (if i.val = 34 then (1 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_28 (i : Fin 45) :
    integerJacobian i 28 = tableIntegerJacobian i 28 := by
  unfold integerJacobian
  rw [column_expansion_28, table_column_values_28]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_28
#assert_trust kernel column_table_match_28

theorem column_expansion_29 : integerDerivativeColumns 29 = C (1 : ℤ) * X ^ 20 + C (1 : ℤ) * X ^ 21 + C (1 : ℤ) * X ^ 29 + C (1 : ℤ) * X ^ 34 + C (1 : ℤ) * X ^ 36 + C (1 : ℤ) * X ^ 39 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_29 : ∀ i : Fin 45,
    tableIntegerJacobian i 29 = (if i.val = 20 then (1 : ℤ) else 0) + (if i.val = 21 then (1 : ℤ) else 0) + (if i.val = 29 then (1 : ℤ) else 0) + (if i.val = 34 then (1 : ℤ) else 0) + (if i.val = 36 then (1 : ℤ) else 0) + (if i.val = 39 then (1 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_29 (i : Fin 45) :
    integerJacobian i 29 = tableIntegerJacobian i 29 := by
  unfold integerJacobian
  rw [column_expansion_29, table_column_values_29]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_29
#assert_trust kernel column_table_match_29

end Mod3Certificate
end NLA.MF14Degree44
