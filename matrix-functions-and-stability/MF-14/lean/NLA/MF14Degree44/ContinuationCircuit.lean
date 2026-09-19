/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial Codex assistance. Marcus Webb retains mathematical authorship.

The exact continuation appends three gates to one witness for the four shared
inputs. Every operand is shown to lie in the chronological available span.
-/
import NLA.MF14Degree44.CircuitSpanOperations

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
namespace NLA.MF14Degree44

theorem continuation_actual_output (theta : Parameters) (v : Quad)
    (hv : JointFourAvailable v) :
    NLA.MF14.IsSevenProductOutput (continuationPolynomial theta v) := by
  classical
  obtain ⟨q4, hq4, hv4⟩ := hv
  let l3 : Fin 3 → Poly := ![X, v 0, v 1]
  let l4 : Fin 4 → Poly := ![X, v 0, v 1, v 2]
  let l5 : Fin 5 → Poly := ![X, v 0, v 1, v 2, v 3]
  have hl3 : ∀ i : Fin 3, l3 i ∈ NLA.MF14.availableSpace q4 4 := by
    intro i
    fin_cases i
    · exact available_X q4 4
    · exact hv4 0
    · exact hv4 1
  have hl4 : ∀ i : Fin 4, l4 i ∈ NLA.MF14.availableSpace q4 4 := by
    intro i
    fin_cases i
    · exact available_X q4 4
    · exact hv4 0
    · exact hv4 1
    · exact hv4 2
  have hl5 : ∀ i : Fin 5, l5 i ∈ NLA.MF14.availableSpace q4 4 := by
    intro i
    fin_cases i
    · exact available_X q4 4
    · exact hv4 0
    · exact hv4 1
    · exact hv4 2
    · exact hv4 3
  let f0 : Poly := v 3 +
    linearCombination (fun i : Fin 4 => theta (parameterIndex 9 (by decide) i)) l4
  let f1 : Poly := v 2 +
    linearCombination (fun i : Fin 3 => theta (parameterIndex 13 (by decide) i)) l3
  let f : Poly := f0 * f1
  have hf0 : f0 ∈ NLA.MF14.availableSpace q4 4 :=
    (NLA.MF14.availableSpace q4 4).add_mem (hv4 3)
      (linearCombination_mem _ _ l4 hl4)
  have hf1 : f1 ∈ NLA.MF14.availableSpace q4 4 :=
    (NLA.MF14.availableSpace q4 4).add_mem (hv4 2)
      (linearCombination_mem _ _ l3 hl3)
  obtain ⟨q5, hq5, h45, hf⟩ :=
    append_product_to_prefix q4 (4 : Fin 7) hq4 f0 f1 hf0 hf1
  change f ∈ NLA.MF14.availableSpace q5 5 at hf
  let g0 : Poly := f +
    linearCombination (fun i : Fin 5 => theta (parameterIndex 16 (by decide) i)) l5
  let g1 : Poly := v 2 +
    linearCombination (fun i : Fin 3 => theta (parameterIndex 21 (by decide) i)) l3
  let g : Poly := g0 * g1
  have hg0 : g0 ∈ NLA.MF14.availableSpace q5 5 :=
    (NLA.MF14.availableSpace q5 5).add_mem hf
      (linearCombination_mem _ _ l5 (fun i => h45 (hl5 i)))
  have hg1 : g1 ∈ NLA.MF14.availableSpace q5 5 :=
    (NLA.MF14.availableSpace q5 5).add_mem (h45 (hv4 2))
      (linearCombination_mem _ _ l3 (fun i => h45 (hl3 i)))
  obtain ⟨q6, hq6, h56, hg⟩ :=
    append_product_to_prefix q5 (5 : Fin 7) hq5 g0 g1 hg0 hg1
  change g ∈ NLA.MF14.availableSpace q6 6 at hg
  let l6 : Fin 6 → Poly := ![X, v 0, v 1, v 2, v 3, f]
  have hl6 : ∀ i : Fin 6, l6 i ∈ NLA.MF14.availableSpace q6 6 := by
    intro i
    fin_cases i
    · exact available_X q6 6
    · exact h56 (h45 (hv4 0))
    · exact h56 (h45 (hv4 1))
    · exact h56 (h45 (hv4 2))
    · exact h56 (h45 (hv4 3))
    · exact h56 hf
  let h0 : Poly := g +
    linearCombination (fun i : Fin 6 => theta (parameterIndex 24 (by decide) i)) l6
  let h1 : Poly := g +
    linearCombination (fun i : Fin 6 => theta (parameterIndex 30 (by decide) i)) l6
  let h : Poly := h0 * h1
  have hh0 : h0 ∈ NLA.MF14.availableSpace q6 6 :=
    (NLA.MF14.availableSpace q6 6).add_mem hg
      (linearCombination_mem _ _ l6 hl6)
  have hh1 : h1 ∈ NLA.MF14.availableSpace q6 6 :=
    (NLA.MF14.availableSpace q6 6).add_mem hg
      (linearCombination_mem _ _ l6 hl6)
  obtain ⟨q7, hq7, h67, hh⟩ :=
    append_product_to_prefix q6 (6 : Fin 7) hq6 h0 h1 hh0 hh1
  change h ∈ NLA.MF14.availableSpace q7 7 at hh
  have hb : ∀ i : Fin 9, continuationBasis theta v i ∈ NLA.MF14.availableSpace q7 7 := by
    intro i
    fin_cases i
    · change (1 : Poly) ∈ NLA.MF14.availableSpace q7 7
      exact available_one q7 7
    · change (X : Poly) ∈ NLA.MF14.availableSpace q7 7
      exact available_X q7 7
    · change v 0 ∈ NLA.MF14.availableSpace q7 7
      exact h67 (h56 (h45 (hv4 0)))
    · change v 1 ∈ NLA.MF14.availableSpace q7 7
      exact h67 (h56 (h45 (hv4 1)))
    · change v 2 ∈ NLA.MF14.availableSpace q7 7
      exact h67 (h56 (h45 (hv4 2)))
    · change v 3 ∈ NLA.MF14.availableSpace q7 7
      exact h67 (h56 (h45 (hv4 3)))
    · change f ∈ NLA.MF14.availableSpace q7 7
      exact h67 (h56 hf)
    · change g ∈ NLA.MF14.availableSpace q7 7
      exact h67 hg
    · change h ∈ NLA.MF14.availableSpace q7 7
      exact hh
  refine ⟨q7, fun k => hq7.2 k k.isLt, ?_⟩
  unfold continuationPolynomial
  exact linearCombination_mem _ _ _ hb

#print axioms continuation_actual_output
#assert_trust kernel continuation_actual_output
end NLA.MF14Degree44
