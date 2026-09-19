/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial Codex assistance. Marcus Webb retains mathematical authorship.

Small exact whole-polynomial direction partition. No numerical sample,
coefficient truncation, or stored derivative equality is assumed.
-/
import NLA.MF14Degree44.FamilyFirstJet

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
open scoped BigOperators
namespace NLA.MF14Degree44

theorem seed_first_column_2 :
    (familyFirstJet basePoint).first (2 : Fin 45) =
      (integerDerivativeColumns 2).map (Int.castRingHom ℂ) := by
  simp [familyFirstJet, continuationFirstBasis, familyFirstQuad,
    PolyFirstJet.const, PolyFirstJet.coordinate, PolyFirstJet.add,
    PolyFirstJet.mul, PolyFirstJet.parameterCombination, PolyFirstJet.finsetSum,
    basePoint, parameterIndex, integerDerivativeColumns, Fin.sum_univ_succ]
  <;> ring

#print axioms seed_first_column_2
#assert_trust kernel seed_first_column_2

theorem seed_first_column_3 :
    (familyFirstJet basePoint).first (3 : Fin 45) =
      (integerDerivativeColumns 3).map (Int.castRingHom ℂ) := by
  simp [familyFirstJet, continuationFirstBasis, familyFirstQuad,
    PolyFirstJet.const, PolyFirstJet.coordinate, PolyFirstJet.add,
    PolyFirstJet.mul, PolyFirstJet.parameterCombination, PolyFirstJet.finsetSum,
    basePoint, parameterIndex, integerDerivativeColumns, Fin.sum_univ_succ]
  <;> ring

#print axioms seed_first_column_3
#assert_trust kernel seed_first_column_3

theorem seed_first_column_4 :
    (familyFirstJet basePoint).first (4 : Fin 45) =
      (integerDerivativeColumns 4).map (Int.castRingHom ℂ) := by
  simp [familyFirstJet, continuationFirstBasis, familyFirstQuad,
    PolyFirstJet.const, PolyFirstJet.coordinate, PolyFirstJet.add,
    PolyFirstJet.mul, PolyFirstJet.parameterCombination, PolyFirstJet.finsetSum,
    basePoint, parameterIndex, integerDerivativeColumns, Fin.sum_univ_succ]
  <;> ring

#print axioms seed_first_column_4
#assert_trust kernel seed_first_column_4

end NLA.MF14Degree44
