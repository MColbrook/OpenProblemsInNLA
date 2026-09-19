import NLA.MF14Degree44.Family
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic
import LeanCert.Tactic.Verification

/-!
Exact degree bounds for Marcus Webb's continuation, The University of Manchester.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; Codex assistance.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
open scoped BigOperators
namespace NLA.MF14Degree44

lemma linearCombination_natDegree_le {m d : ℕ} (c : Fin m → ℂ) (v : Fin m → Poly)
    (hv : ∀ i, (v i).natDegree ≤ d) : (linearCombination c v).natDegree ≤ d := by
  unfold linearCombination
  exact natDegree_sum_le_of_forall_le Finset.univ _
    (fun i _ => (natDegree_C_mul_le (c i) (v i)).trans (hv i))

lemma continuation_natDegree_of_bounds (theta : Parameters) (v : Quad) (d e : ℕ)
    (he : 1 ≤ e) (hed : e ≤ d)
    (h0 : (v 0).natDegree ≤ e) (h1 : (v 1).natDegree ≤ e)
    (h2 : (v 2).natDegree ≤ e) (h3 : (v 3).natDegree ≤ d) :
    (continuationPolynomial theta v).natDegree ≤ 2 * (d + e + e) := by
  let l3 : Fin 3 → Poly := ![X, v 0, v 1]
  let l4 : Fin 4 → Poly := ![X, v 0, v 1, v 2]
  let l5 : Fin 5 → Poly := ![X, v 0, v 1, v 2, v 3]
  have hx : (X : Poly).natDegree ≤ e := natDegree_X_le.trans he
  have hsmall : ∀ i, (l3 i).natDegree ≤ e := by
    intro i; fin_cases i
    · exact hx
    · exact h0
    · exact h1
  have hfour : ∀ i, (l4 i).natDegree ≤ d := by
    intro i; fin_cases i
    · exact hx.trans hed
    · exact h0.trans hed
    · exact h1.trans hed
    · exact h2.trans hed
  have hfive : ∀ i, (l5 i).natDegree ≤ d := by
    intro i; fin_cases i
    · exact hx.trans hed
    · exact h0.trans hed
    · exact h1.trans hed
    · exact h2.trans hed
    · exact h3
  let f :=
    (v 3 + linearCombination (fun i : Fin 4 => theta (parameterIndex 9 (by decide) i)) l4) *
    (v 2 + linearCombination (fun i : Fin 3 => theta (parameterIndex 13 (by decide) i)) l3)
  have hf : f.natDegree ≤ d + e := by
    apply natDegree_mul_le.trans
    exact Nat.add_le_add
      (natDegree_add_le_of_degree_le h3 (linearCombination_natDegree_le _ _ hfour))
      (natDegree_add_le_of_degree_le h2 (linearCombination_natDegree_le _ _ hsmall))
  let g :=
    (f + linearCombination (fun i : Fin 5 => theta (parameterIndex 16 (by decide) i)) l5) *
    (v 2 + linearCombination (fun i : Fin 3 => theta (parameterIndex 21 (by decide) i)) l3)
  have hg : g.natDegree ≤ d + e + e := by
    apply natDegree_mul_le.trans
    exact Nat.add_le_add
      (natDegree_add_le_of_degree_le hf
        ((linearCombination_natDegree_le _ _ hfive).trans (by omega)))
      (natDegree_add_le_of_degree_le h2 (linearCombination_natDegree_le _ _ hsmall))
  let l6 : Fin 6 → Poly := ![X, v 0, v 1, v 2, v 3, f]
  have hsix : ∀ i, (l6 i).natDegree ≤ d + e + e := by
    intro i; fin_cases i
    · exact hx.trans (by omega)
    · exact h0.trans (by omega)
    · exact h1.trans (by omega)
    · exact h2.trans (by omega)
    · exact h3.trans (by omega)
    · exact hf.trans (by omega)
  let h :=
    (g + linearCombination (fun i : Fin 6 => theta (parameterIndex 24 (by decide) i)) l6) *
    (g + linearCombination (fun i : Fin 6 => theta (parameterIndex 30 (by decide) i)) l6)
  have hh : h.natDegree ≤ 2 * (d + e + e) := by
    have hleft := natDegree_add_le_of_degree_le hg (linearCombination_natDegree_le
      (fun i : Fin 6 => theta (parameterIndex 24 (by decide) i)) _ hsix)
    have hright := natDegree_add_le_of_degree_le hg (linearCombination_natDegree_le
      (fun i : Fin 6 => theta (parameterIndex 30 (by decide) i)) _ hsix)
    exact natDegree_mul_le.trans ((Nat.add_le_add hleft hright).trans (by omega))
  change (linearCombination _ ![1, X, v 0, v 1, v 2, v 3, f, g, h]).natDegree ≤ _
  apply linearCombination_natDegree_le
  intro i; fin_cases i
  · simp
  · exact hx.trans (by omega)
  · exact h0.trans (by omega)
  · exact h1.trans (by omega)
  · exact h2.trans (by omega)
  · exact h3.trans (by omega)
  · exact hf.trans (by omega)
  · exact hg.trans (by omega)
  · exact hh

lemma decodeQuad_natDegree (z : QuadSpace) (i : Fin 4) :
    (decodeQuad z i).natDegree ≤ 16 := by
  unfold decodeQuad
  apply natDegree_sum_le_of_forall_le Finset.univ
  intro k _
  exact (natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le k.val).trans (by omega))

theorem continuation_degree_bound (theta : Parameters) (z : QuadSpace) :
    (continuationPolynomial theta (decodeQuad z)).natDegree ≤ 96 := by
  exact continuation_natDegree_of_bounds theta (decodeQuad z) 16 16 (by decide) le_rfl
    (decodeQuad_natDegree z 0) (decodeQuad_natDegree z 1)
    (decodeQuad_natDegree z 2) (decodeQuad_natDegree z 3)

lemma monicBorderPolynomial_natDegree (xi : Fin 7 → ℂ) :
    (monicBorderPolynomial xi).natDegree ≤ 12 := by
  unfold monicBorderPolynomial
  exact (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (natDegree_X_pow_le 12) ((natDegree_C_mul_le (xi 0) (X ^ 3)).trans ((natDegree_X_pow_le 3).trans (by decide)))) ((natDegree_C_mul_le (xi 1) (X ^ 6)).trans ((natDegree_X_pow_le 6).trans (by decide)))) ((natDegree_C_mul_le (xi 2) (X ^ 7)).trans ((natDegree_X_pow_le 7).trans (by decide)))) ((natDegree_C_mul_le (xi 3) (X ^ 8)).trans ((natDegree_X_pow_le 8).trans (by decide)))) ((natDegree_C_mul_le (xi 4) (X ^ 9)).trans ((natDegree_X_pow_le 9).trans (by decide)))) ((natDegree_C_mul_le (xi 5) (X ^ 10)).trans ((natDegree_X_pow_le 10).trans (by decide)))) ((natDegree_C_mul_le (xi 6) (X ^ 11)).trans ((natDegree_X_pow_le 11).trans (by decide))))

#print axioms continuation_degree_bound
#assert_trust kernel continuation_degree_bound

end NLA.MF14Degree44
