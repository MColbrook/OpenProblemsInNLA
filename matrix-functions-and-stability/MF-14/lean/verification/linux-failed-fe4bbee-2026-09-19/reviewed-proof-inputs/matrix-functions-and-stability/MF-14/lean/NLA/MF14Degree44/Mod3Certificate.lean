import NLA.MF14Degree44.Mod3Columns0
import NLA.MF14Degree44.Mod3Columns1
import NLA.MF14Degree44.Mod3Columns2
import NLA.MF14Degree44.Mod3Columns3
import NLA.MF14Degree44.Mod3Columns4
import NLA.MF14Degree44.Mod3Columns5
import NLA.MF14Degree44.Mod3Columns6
import NLA.MF14Degree44.Mod3Columns7
import NLA.MF14Degree44.Mod3Columns8
import NLA.MF14Degree44.Mod3Rows0
import NLA.MF14Degree44.Mod3Rows1
import NLA.MF14Degree44.Mod3Rows2
import NLA.MF14Degree44.Mod3Rows3
import NLA.MF14Degree44.Mod3Rows4
import NLA.MF14Degree44.Mod3Rows5
import NLA.MF14Degree44.Mod3Rows6
import NLA.MF14Degree44.Mod3Rows7
import NLA.MF14Degree44.Mod3Rows8
import NLA.MF14Degree44.Mod3CastBridge

/-!
Complete exact modular witness, transferred from checked natural-number dot
products and symbolic polynomial columns. Original construction: Marcus Webb,
The University of Manchester. Formalization: George Stepaniants, Department
of Computing and Mathematical Sciences, California Institute of Technology;
Codex assistance. The derivative/table identity remains a separate obligation.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped Matrix
noncomputable section
namespace NLA.MF14Degree44
open Mod3Certificate

theorem integerJacobian_eq_checked_table : integerJacobian = tableIntegerJacobian := by
  ext i j
  fin_cases j
  · exact column_table_match_0 i
  · exact column_table_match_1 i
  · exact column_table_match_2 i
  · exact column_table_match_3 i
  · exact column_table_match_4 i
  · exact column_table_match_5 i
  · exact column_table_match_6 i
  · exact column_table_match_7 i
  · exact column_table_match_8 i
  · exact column_table_match_9 i
  · exact column_table_match_10 i
  · exact column_table_match_11 i
  · exact column_table_match_12 i
  · exact column_table_match_13 i
  · exact column_table_match_14 i
  · exact column_table_match_15 i
  · exact column_table_match_16 i
  · exact column_table_match_17 i
  · exact column_table_match_18 i
  · exact column_table_match_19 i
  · exact column_table_match_20 i
  · exact column_table_match_21 i
  · exact column_table_match_22 i
  · exact column_table_match_23 i
  · exact column_table_match_24 i
  · exact column_table_match_25 i
  · exact column_table_match_26 i
  · exact column_table_match_27 i
  · exact column_table_match_28 i
  · exact column_table_match_29 i
  · exact column_table_match_30 i
  · exact column_table_match_31 i
  · exact column_table_match_32 i
  · exact column_table_match_33 i
  · exact column_table_match_34 i
  · exact column_table_match_35 i
  · exact column_table_match_36 i
  · exact column_table_match_37 i
  · exact column_table_match_38 i
  · exact column_table_match_39 i
  · exact column_table_match_40 i
  · exact column_table_match_41 i
  · exact column_table_match_42 i
  · exact column_table_match_43 i
  · exact column_table_match_44 i

theorem mod3_checked_table_inverse : tableJacobianMod3 * tableInverseMod3 = 1 := by
  ext i j
  apply matrix_entry_of_natural_residue
  fin_cases i
  · exact natural_inverse_row_0 j
  · exact natural_inverse_row_1 j
  · exact natural_inverse_row_2 j
  · exact natural_inverse_row_3 j
  · exact natural_inverse_row_4 j
  · exact natural_inverse_row_5 j
  · exact natural_inverse_row_6 j
  · exact natural_inverse_row_7 j
  · exact natural_inverse_row_8 j
  · exact natural_inverse_row_9 j
  · exact natural_inverse_row_10 j
  · exact natural_inverse_row_11 j
  · exact natural_inverse_row_12 j
  · exact natural_inverse_row_13 j
  · exact natural_inverse_row_14 j
  · exact natural_inverse_row_15 j
  · exact natural_inverse_row_16 j
  · exact natural_inverse_row_17 j
  · exact natural_inverse_row_18 j
  · exact natural_inverse_row_19 j
  · exact natural_inverse_row_20 j
  · exact natural_inverse_row_21 j
  · exact natural_inverse_row_22 j
  · exact natural_inverse_row_23 j
  · exact natural_inverse_row_24 j
  · exact natural_inverse_row_25 j
  · exact natural_inverse_row_26 j
  · exact natural_inverse_row_27 j
  · exact natural_inverse_row_28 j
  · exact natural_inverse_row_29 j
  · exact natural_inverse_row_30 j
  · exact natural_inverse_row_31 j
  · exact natural_inverse_row_32 j
  · exact natural_inverse_row_33 j
  · exact natural_inverse_row_34 j
  · exact natural_inverse_row_35 j
  · exact natural_inverse_row_36 j
  · exact natural_inverse_row_37 j
  · exact natural_inverse_row_38 j
  · exact natural_inverse_row_39 j
  · exact natural_inverse_row_40 j
  · exact natural_inverse_row_41 j
  · exact natural_inverse_row_42 j
  · exact natural_inverse_row_43 j
  · exact natural_inverse_row_44 j

theorem integerJacobianMod3_eq_checked_table : integerJacobianMod3 = tableJacobianMod3 := by
  ext i j
  change (integerJacobian i j : ZMod 3) = (jacobianEntryNat i j : ZMod 3)
  rw [integerJacobian_eq_checked_table]
  simp only [tableIntegerJacobian, Int.cast_natCast]

theorem integer_jacobian_mod3_inverse :
    ∃ B : Matrix (Fin 45) (Fin 45) (ZMod 3), integerJacobianMod3 * B = 1 := by
  refine ⟨tableInverseMod3, ?_⟩
  rw [integerJacobianMod3_eq_checked_table]
  exact mod3_checked_table_inverse

#print axioms integerJacobian_eq_checked_table
#assert_trust kernel integerJacobian_eq_checked_table
#print axioms mod3_checked_table_inverse
#assert_trust kernel mod3_checked_table_inverse
#print axioms integerJacobianMod3_eq_checked_table
#assert_trust kernel integerJacobianMod3_eq_checked_table
#print axioms integer_jacobian_mod3_inverse
#assert_trust kernel integer_jacobian_mod3_inverse

end NLA.MF14Degree44
