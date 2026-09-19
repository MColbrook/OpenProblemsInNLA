/- Complete finite coverage of the 45 exact whole-polynomial identities. -/
import NLA.MF14Degree44.SeedFirstPilot
import NLA.MF14Degree44.SeedFirstColumns0
import NLA.MF14Degree44.SeedFirstColumns1
import NLA.MF14Degree44.SeedFirstColumns2
import NLA.MF14Degree44.SeedFirstColumns3
import NLA.MF14Degree44.SeedFirstColumns4
import NLA.MF14Degree44.SeedFirstColumns5
import NLA.MF14Degree44.SeedFirstColumns6
import NLA.MF14Degree44.SeedFirstColumns7
import NLA.MF14Degree44.SeedFirstColumns8

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.MF14Degree44

theorem seed_first_columns (j : Fin 45) :
    (familyFirstJet basePoint).first j =
      (integerDerivativeColumns j).map (Int.castRingHom ℂ) := by
  fin_cases j
  · exact seed_first_column_0
  · exact seed_first_column_1
  · exact seed_first_column_2
  · exact seed_first_column_3
  · exact seed_first_column_4
  · exact seed_first_column_5
  · exact seed_first_column_6
  · exact seed_first_column_7
  · exact seed_first_column_8
  · exact seed_first_column_9
  · exact seed_first_column_10
  · exact seed_first_column_11
  · exact seed_first_column_12
  · exact seed_first_column_13
  · exact seed_first_column_14
  · exact seed_first_column_15
  · exact seed_first_column_16
  · exact seed_first_column_17
  · exact seed_first_column_18
  · exact seed_first_column_19
  · exact seed_first_column_20
  · exact seed_first_column_21
  · exact seed_first_column_22
  · exact seed_first_column_23
  · exact seed_first_column_24
  · exact seed_first_column_25
  · exact seed_first_column_26
  · exact seed_first_column_27
  · exact seed_first_column_28
  · exact seed_first_column_29
  · exact seed_first_column_30
  · exact seed_first_column_31
  · exact seed_first_column_32
  · exact seed_first_column_33
  · exact seed_first_column_34
  · exact seed_first_column_35
  · exact seed_first_column_36
  · exact seed_first_column_37
  · exact seed_first_column_38
  · exact seed_first_column_39
  · exact seed_first_column_40
  · exact seed_first_column_41
  · exact seed_first_column_42
  · exact seed_first_column_43
  · exact seed_first_column_44

#print axioms seed_first_columns
#assert_trust kernel seed_first_columns
end NLA.MF14Degree44
