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

theorem seed_first_column_30 :
    (familyFirstJet basePoint).first (30 : Fin 45) =
      (integerDerivativeColumns 30).map (Int.castRingHom ℂ) := by
  simp [familyFirstJet, continuationFirstBasis, familyFirstQuad,
    PolyFirstJet.const, PolyFirstJet.coordinate, PolyFirstJet.add,
    PolyFirstJet.mul, PolyFirstJet.parameterCombination, PolyFirstJet.finsetSum,
    basePoint, parameterIndex, integerDerivativeColumns, Fin.sum_univ_succ]
  <;> ring <;> simp

#print axioms seed_first_column_30
#assert_trust kernel seed_first_column_30

theorem seed_first_column_31 :
    (familyFirstJet basePoint).first (31 : Fin 45) =
      (integerDerivativeColumns 31).map (Int.castRingHom ℂ) := by
  simp [familyFirstJet, continuationFirstBasis, familyFirstQuad,
    PolyFirstJet.const, PolyFirstJet.coordinate, PolyFirstJet.add,
    PolyFirstJet.mul, PolyFirstJet.parameterCombination, PolyFirstJet.finsetSum,
    basePoint, parameterIndex, integerDerivativeColumns, Fin.sum_univ_succ]
  <;> ring <;> simp

#print axioms seed_first_column_31
#assert_trust kernel seed_first_column_31

theorem seed_first_column_32 :
    (familyFirstJet basePoint).first (32 : Fin 45) =
      (integerDerivativeColumns 32).map (Int.castRingHom ℂ) := by
  simp [familyFirstJet, continuationFirstBasis, familyFirstQuad,
    PolyFirstJet.const, PolyFirstJet.coordinate, PolyFirstJet.add,
    PolyFirstJet.mul, PolyFirstJet.parameterCombination, PolyFirstJet.finsetSum,
    basePoint, parameterIndex, integerDerivativeColumns, Fin.sum_univ_succ]
  <;> ring <;> simp

#print axioms seed_first_column_32
#assert_trust kernel seed_first_column_32

theorem seed_first_column_33 :
    (familyFirstJet basePoint).first (33 : Fin 45) =
      (integerDerivativeColumns 33).map (Int.castRingHom ℂ) := by
  simp [familyFirstJet, continuationFirstBasis, familyFirstQuad,
    PolyFirstJet.const, PolyFirstJet.coordinate, PolyFirstJet.add,
    PolyFirstJet.mul, PolyFirstJet.parameterCombination, PolyFirstJet.finsetSum,
    basePoint, parameterIndex, integerDerivativeColumns, Fin.sum_univ_succ]
  <;> ring <;> simp

#print axioms seed_first_column_33
#assert_trust kernel seed_first_column_33

theorem seed_first_column_34 :
    (familyFirstJet basePoint).first (34 : Fin 45) =
      (integerDerivativeColumns 34).map (Int.castRingHom ℂ) := by
  simp [familyFirstJet, continuationFirstBasis, familyFirstQuad,
    PolyFirstJet.const, PolyFirstJet.coordinate, PolyFirstJet.add,
    PolyFirstJet.mul, PolyFirstJet.parameterCombination, PolyFirstJet.finsetSum,
    basePoint, parameterIndex, integerDerivativeColumns, Fin.sum_univ_succ]
  <;> ring <;> simp

#print axioms seed_first_column_34
#assert_trust kernel seed_first_column_34

end NLA.MF14Degree44
