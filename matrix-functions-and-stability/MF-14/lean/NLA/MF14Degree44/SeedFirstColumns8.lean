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

theorem seed_first_column_40 :
    (familyFirstJet basePoint).first (40 : Fin 45) =
      (integerDerivativeColumns 40).map (Int.castRingHom ℂ) := by
  simp [familyFirstJet, continuationFirstBasis, familyFirstQuad,
    PolyFirstJet.const, PolyFirstJet.coordinate, PolyFirstJet.add,
    PolyFirstJet.mul, PolyFirstJet.parameterCombination, PolyFirstJet.finsetSum,
    basePoint, parameterIndex, integerDerivativeColumns, Fin.sum_univ_succ]
  <;> ring

#print axioms seed_first_column_40
#assert_trust kernel seed_first_column_40

theorem seed_first_column_41 :
    (familyFirstJet basePoint).first (41 : Fin 45) =
      (integerDerivativeColumns 41).map (Int.castRingHom ℂ) := by
  simp [familyFirstJet, continuationFirstBasis, familyFirstQuad,
    PolyFirstJet.const, PolyFirstJet.coordinate, PolyFirstJet.add,
    PolyFirstJet.mul, PolyFirstJet.parameterCombination, PolyFirstJet.finsetSum,
    basePoint, parameterIndex, integerDerivativeColumns, Fin.sum_univ_succ]
  <;> ring

#print axioms seed_first_column_41
#assert_trust kernel seed_first_column_41

theorem seed_first_column_42 :
    (familyFirstJet basePoint).first (42 : Fin 45) =
      (integerDerivativeColumns 42).map (Int.castRingHom ℂ) := by
  simp [familyFirstJet, continuationFirstBasis, familyFirstQuad,
    PolyFirstJet.const, PolyFirstJet.coordinate, PolyFirstJet.add,
    PolyFirstJet.mul, PolyFirstJet.parameterCombination, PolyFirstJet.finsetSum,
    basePoint, parameterIndex, integerDerivativeColumns, Fin.sum_univ_succ]
  <;> ring

#print axioms seed_first_column_42
#assert_trust kernel seed_first_column_42

theorem seed_first_column_43 :
    (familyFirstJet basePoint).first (43 : Fin 45) =
      (integerDerivativeColumns 43).map (Int.castRingHom ℂ) := by
  simp [familyFirstJet, continuationFirstBasis, familyFirstQuad,
    PolyFirstJet.const, PolyFirstJet.coordinate, PolyFirstJet.add,
    PolyFirstJet.mul, PolyFirstJet.parameterCombination, PolyFirstJet.finsetSum,
    basePoint, parameterIndex, integerDerivativeColumns, Fin.sum_univ_succ]
  <;> ring

#print axioms seed_first_column_43
#assert_trust kernel seed_first_column_43

theorem seed_first_column_44 :
    (familyFirstJet basePoint).first (44 : Fin 45) =
      (integerDerivativeColumns 44).map (Int.castRingHom ℂ) := by
  simp [familyFirstJet, continuationFirstBasis, familyFirstQuad,
    PolyFirstJet.const, PolyFirstJet.coordinate, PolyFirstJet.add,
    PolyFirstJet.mul, PolyFirstJet.parameterCombination, PolyFirstJet.finsetSum,
    basePoint, parameterIndex, integerDerivativeColumns, Fin.sum_univ_succ]
  <;> ring

#print axioms seed_first_column_44
#assert_trust kernel seed_first_column_44

end NLA.MF14Degree44
