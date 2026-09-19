import NLA.MF14Degree44.Mod3Lists

set_option autoImplicit false
open Polynomial
open scoped BigOperators Matrix
noncomputable section
namespace NLA.MF14Degree44
namespace Mod3Certificate

theorem column_expansion_40 : integerDerivativeColumns 40 = C (1 : ℤ) * X ^ 5 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_40 : ∀ i : Fin 45,
    tableIntegerJacobian i 40 = (if i.val = 5 then (1 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_40 (i : Fin 45) :
    integerJacobian i 40 = tableIntegerJacobian i 40 := by
  unfold integerJacobian
  rw [column_expansion_40, table_column_values_40]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_40
#assert_trust kernel column_table_match_40

theorem column_expansion_41 : integerDerivativeColumns 41 = C (1 : ℤ) * X ^ 12 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_41 : ∀ i : Fin 45,
    tableIntegerJacobian i 41 = (if i.val = 12 then (1 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_41 (i : Fin 45) :
    integerJacobian i 41 = tableIntegerJacobian i 41 := by
  unfold integerJacobian
  rw [column_expansion_41, table_column_values_41]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_41
#assert_trust kernel column_table_match_41

theorem column_expansion_42 : integerDerivativeColumns 42 = C (1 : ℤ) * X ^ 17 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_42 : ∀ i : Fin 45,
    tableIntegerJacobian i 42 = (if i.val = 17 then (1 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_42 (i : Fin 45) :
    integerJacobian i 42 = tableIntegerJacobian i 42 := by
  unfold integerJacobian
  rw [column_expansion_42, table_column_values_42]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_42
#assert_trust kernel column_table_match_42

theorem column_expansion_43 : integerDerivativeColumns 43 = C (1 : ℤ) * X ^ 19 + C (1 : ℤ) * X ^ 22 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_43 : ∀ i : Fin 45,
    tableIntegerJacobian i 43 = (if i.val = 19 then (1 : ℤ) else 0) + (if i.val = 22 then (1 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_43 (i : Fin 45) :
    integerJacobian i 43 = tableIntegerJacobian i 43 := by
  unfold integerJacobian
  rw [column_expansion_43, table_column_values_43]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_43
#assert_trust kernel column_table_match_43

theorem column_expansion_44 : integerDerivativeColumns 44 = C (1 : ℤ) * X ^ 22 + C (1 : ℤ) * X ^ 23 + C (1 : ℤ) * X ^ 25 + C (1 : ℤ) * X ^ 26 + C (1 : ℤ) * X ^ 31 + C (1 : ℤ) * X ^ 34 + C (1 : ℤ) * X ^ 36 + C (1 : ℤ) * X ^ 38 + C (1 : ℤ) * X ^ 39 + C (2 : ℤ) * X ^ 41 + C (1 : ℤ) * X ^ 44 := by
  dsimp [integerDerivativeColumns]
  norm_num only [map_ofNat, map_one]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem table_column_values_44 : ∀ i : Fin 45,
    tableIntegerJacobian i 44 = (if i.val = 22 then (1 : ℤ) else 0) + (if i.val = 23 then (1 : ℤ) else 0) + (if i.val = 25 then (1 : ℤ) else 0) + (if i.val = 26 then (1 : ℤ) else 0) + (if i.val = 31 then (1 : ℤ) else 0) + (if i.val = 34 then (1 : ℤ) else 0) + (if i.val = 36 then (1 : ℤ) else 0) + (if i.val = 38 then (1 : ℤ) else 0) + (if i.val = 39 then (1 : ℤ) else 0) + (if i.val = 41 then (2 : ℤ) else 0) + (if i.val = 44 then (1 : ℤ) else 0) := by
  decide +kernel

theorem column_table_match_44 (i : Fin 45) :
    integerJacobian i 44 = tableIntegerJacobian i 44 := by
  unfold integerJacobian
  rw [column_expansion_44, table_column_values_44]
  simp only [coeff_add, coeff_C_mul_X_pow]

#print axioms column_table_match_44
#assert_trust kernel column_table_match_44

end Mod3Certificate
end NLA.MF14Degree44
