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

theorem seed_first_column_5 :
    (familyFirstJet basePoint).first (5 : Fin 45) =
      (integerDerivativeColumns 5).map (Int.castRingHom ℂ) := by
  simp [familyFirstJet, continuationFirstBasis, familyFirstQuad,
    PolyFirstJet.const, PolyFirstJet.coordinate, PolyFirstJet.add,
    PolyFirstJet.mul, PolyFirstJet.parameterCombination, PolyFirstJet.finsetSum,
    basePoint, parameterIndex, integerDerivativeColumns, Fin.sum_univ_succ]
  <;> ring

#print axioms seed_first_column_5
#assert_trust kernel seed_first_column_5

theorem seed_first_column_6 :
    (familyFirstJet basePoint).first (6 : Fin 45) =
      (integerDerivativeColumns 6).map (Int.castRingHom ℂ) := by
  simp [familyFirstJet, continuationFirstBasis, familyFirstQuad,
    PolyFirstJet.const, PolyFirstJet.coordinate, PolyFirstJet.add,
    PolyFirstJet.mul, PolyFirstJet.parameterCombination, PolyFirstJet.finsetSum,
    basePoint, parameterIndex, integerDerivativeColumns, Fin.sum_univ_succ]
  <;> ring

#print axioms seed_first_column_6
#assert_trust kernel seed_first_column_6

theorem seed_first_column_7 :
    (familyFirstJet basePoint).first (7 : Fin 45) =
      (integerDerivativeColumns 7).map (Int.castRingHom ℂ) := by
  simp [familyFirstJet, continuationFirstBasis, familyFirstQuad,
    PolyFirstJet.const, PolyFirstJet.coordinate, PolyFirstJet.add,
    PolyFirstJet.mul, PolyFirstJet.parameterCombination, PolyFirstJet.finsetSum,
    basePoint, parameterIndex, integerDerivativeColumns, Fin.sum_univ_succ]
  <;> ring

#print axioms seed_first_column_7
#assert_trust kernel seed_first_column_7

theorem seed_first_column_8 :
    (familyFirstJet basePoint).first (8 : Fin 45) =
      (integerDerivativeColumns 8).map (Int.castRingHom ℂ) := by
  simp [familyFirstJet, continuationFirstBasis, familyFirstQuad,
    PolyFirstJet.const, PolyFirstJet.coordinate, PolyFirstJet.add,
    PolyFirstJet.mul, PolyFirstJet.parameterCombination, PolyFirstJet.finsetSum,
    basePoint, parameterIndex, integerDerivativeColumns, Fin.sum_univ_succ]
  <;> ring

#print axioms seed_first_column_8
#assert_trust kernel seed_first_column_8

theorem seed_first_column_9 :
    (familyFirstJet basePoint).first (9 : Fin 45) =
      (integerDerivativeColumns 9).map (Int.castRingHom ℂ) := by
  simp [familyFirstJet, continuationFirstBasis, familyFirstQuad,
    PolyFirstJet.const, PolyFirstJet.coordinate, PolyFirstJet.add,
    PolyFirstJet.mul, PolyFirstJet.parameterCombination, PolyFirstJet.finsetSum,
    basePoint, parameterIndex, integerDerivativeColumns, Fin.sum_univ_succ]
  <;> ring

#print axioms seed_first_column_9
#assert_trust kernel seed_first_column_9

end NLA.MF14Degree44
