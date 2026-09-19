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

theorem seed_first_column_35 :
    (familyFirstJet basePoint).first (35 : Fin 45) =
      (integerDerivativeColumns 35).map (Int.castRingHom ℂ) := by
  simp [familyFirstJet, continuationFirstBasis, familyFirstQuad,
    PolyFirstJet.const, PolyFirstJet.coordinate, PolyFirstJet.add,
    PolyFirstJet.mul, PolyFirstJet.parameterCombination, PolyFirstJet.finsetSum,
    basePoint, parameterIndex, integerDerivativeColumns, Fin.sum_univ_succ]
  <;> ring

#print axioms seed_first_column_35
#assert_trust kernel seed_first_column_35

theorem seed_first_column_36 :
    (familyFirstJet basePoint).first (36 : Fin 45) =
      (integerDerivativeColumns 36).map (Int.castRingHom ℂ) := by
  simp [familyFirstJet, continuationFirstBasis, familyFirstQuad,
    PolyFirstJet.const, PolyFirstJet.coordinate, PolyFirstJet.add,
    PolyFirstJet.mul, PolyFirstJet.parameterCombination, PolyFirstJet.finsetSum,
    basePoint, parameterIndex, integerDerivativeColumns, Fin.sum_univ_succ]
  <;> ring

#print axioms seed_first_column_36
#assert_trust kernel seed_first_column_36

theorem seed_first_column_37 :
    (familyFirstJet basePoint).first (37 : Fin 45) =
      (integerDerivativeColumns 37).map (Int.castRingHom ℂ) := by
  simp [familyFirstJet, continuationFirstBasis, familyFirstQuad,
    PolyFirstJet.const, PolyFirstJet.coordinate, PolyFirstJet.add,
    PolyFirstJet.mul, PolyFirstJet.parameterCombination, PolyFirstJet.finsetSum,
    basePoint, parameterIndex, integerDerivativeColumns, Fin.sum_univ_succ]
  <;> ring

#print axioms seed_first_column_37
#assert_trust kernel seed_first_column_37

theorem seed_first_column_38 :
    (familyFirstJet basePoint).first (38 : Fin 45) =
      (integerDerivativeColumns 38).map (Int.castRingHom ℂ) := by
  simp [familyFirstJet, continuationFirstBasis, familyFirstQuad,
    PolyFirstJet.const, PolyFirstJet.coordinate, PolyFirstJet.add,
    PolyFirstJet.mul, PolyFirstJet.parameterCombination, PolyFirstJet.finsetSum,
    basePoint, parameterIndex, integerDerivativeColumns, Fin.sum_univ_succ]
  <;> ring

#print axioms seed_first_column_38
#assert_trust kernel seed_first_column_38

theorem seed_first_column_39 :
    (familyFirstJet basePoint).first (39 : Fin 45) =
      (integerDerivativeColumns 39).map (Int.castRingHom ℂ) := by
  simp [familyFirstJet, continuationFirstBasis, familyFirstQuad,
    PolyFirstJet.const, PolyFirstJet.coordinate, PolyFirstJet.add,
    PolyFirstJet.mul, PolyFirstJet.parameterCombination, PolyFirstJet.finsetSum,
    basePoint, parameterIndex, integerDerivativeColumns, Fin.sum_univ_succ]
  <;> ring

#print axioms seed_first_column_39
#assert_trust kernel seed_first_column_39

end NLA.MF14Degree44
