import MF21Restart.NormalizedErrorCoefficient
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

/-- Precisely the nonleading cardinality-m subsets of the actual root list. -/
abbrev BoundaryNonleadingSubset (m : ℕ) (hm : 2 ≤ m) :=
  {s : Finset (Fin (2 * m)) // s.card = m ∧
    s ≠ boundaryLeadingZIndices m (by omega) ∧
    s ≠ boundaryLeadingZInvIndices m (by omega)}

def boundaryErrorTerm (m n : ℕ) (hm : 2 ≤ m)
    (s : BoundaryNonleadingSubset m hm) (theta : ℝ) : ℂ :=
  normalizedErrorCoefficient m (by omega) s.val s.property.1 theta *
    boundaryProductRatio m theta s.val ^ (n + m)

/-- The concrete finite expression corresponding to manuscript (18).
Its identity with the normalized determinant error is a separate obligation. -/
def boundaryErrorExpression (m n : ℕ) (hm : 2 ≤ m) (theta : ℝ) : ℂ := by
  classical
  exact ∑ s : BoundaryNonleadingSubset m hm, boundaryErrorTerm m n hm s theta

theorem boundaryErrorTerm_contDiffAt (m n : ℕ) (hm : 2 ≤ m)
    (s : BoundaryNonleadingSubset m hm) (theta : ℝ)
    (htheta : theta ∈ Set.Icc 0 Real.pi) :
    ContDiffAt ℝ ⊤ (boundaryErrorTerm m n hm s) theta := by
  convert! (normalizedErrorCoefficient_contDiffAt m hm s.val s.property.1 theta
    htheta).mul ((boundaryProductRatio_contDiff m hm s.val).contDiffAt.pow (n + m))
    using 1

theorem boundaryErrorExpression_contDiffAt (m n : ℕ) (hm : 2 ≤ m)
    (theta : ℝ) (htheta : theta ∈ Set.Icc 0 Real.pi) :
    ContDiffAt ℝ ⊤ (boundaryErrorExpression m n hm) theta := by
  classical
  unfold boundaryErrorExpression
  exact ContDiffAt.sum (fun s _ => boundaryErrorTerm_contDiffAt m n hm s theta htheta)

/-- Compactness and finiteness give one bound for the ordinary first derivatives
of all the actual nonleading product ratios. -/
theorem boundaryProductRatio_deriv_uniform_bound (m : ℕ) (hm : 2 ≤ m) :
    ∃ B : ℝ, 0 < B ∧ ∀ s : BoundaryNonleadingSubset m hm,
      ∀ theta ∈ Set.Icc (0 : ℝ) Real.pi,
        ‖deriv (fun t => boundaryProductRatio m t s.val) theta‖ ≤ B := by
  classical
  have hall : ∀ s : BoundaryNonleadingSubset m hm, ∃ B : ℝ, 0 < B ∧
      ∀ theta ∈ Set.Icc (0 : ℝ) Real.pi,
        ‖deriv (fun t => boundaryProductRatio m t s.val) theta‖ ≤ B := by
    intro s
    obtain ⟨B, hB, hbound⟩ := exists_pos_bound_with_deriv_of_contDiffAt_on_Icc
      (fun t => boundaryProductRatio m t s.val)
      (fun _ _ => (boundaryProductRatio_contDiff m hm s.val).contDiffAt)
    exact ⟨B, hB, fun theta htheta => (hbound theta htheta).2⟩
  choose bs hpos hbound using hall
  have hsum0 : 0 ≤ ∑ s : BoundaryNonleadingSubset m hm, bs s :=
    Finset.sum_nonneg (fun s _ => (hpos s).le)
  refine ⟨1 + ∑ s : BoundaryNonleadingSubset m hm, bs s, by linarith, ?_⟩
  intro s theta htheta
  have hle : bs s ≤ ∑ t : BoundaryNonleadingSubset m hm, bs t :=
    Finset.single_le_sum (fun t _ => (hpos t).le) (Finset.mem_univ s)
  linarith [hbound s theta htheta]

private theorem norm_pow_le_exp_of_le (z : ℂ) (c theta : ℝ)
    (hc : 0 ≤ c) (htheta : 0 ≤ theta)
    (hz : ‖z‖ ≤ Real.exp (-c * theta)) (n k : ℕ) (hnk : n ≤ k) :
    ‖z ^ k‖ ≤ Real.exp (-c * (n : ℝ) * theta) := by
  have hnkR : (n : ℝ) ≤ k := by exact_mod_cast hnk
  have hneg : -c * theta ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) htheta
  calc
    ‖z ^ k‖ = ‖z‖ ^ k := norm_pow z k
    _ ≤ Real.exp (-c * theta) ^ k := pow_le_pow_left₀ (norm_nonneg z) hz k
    _ = Real.exp ((k : ℝ) * (-c * theta)) := (Real.exp_nat_mul _ k).symm
    _ ≤ Real.exp ((n : ℝ) * (-c * theta)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hnkR hneg)
    _ = Real.exp (-c * (n : ℝ) * theta) := by congr 1 <;> ring

private theorem norm_product_power_derivative_le
    (a da b db : ℂ) (k : ℕ) (A B E : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (ha : ‖a‖ ≤ A) (hda : ‖da‖ ≤ A) (hdb : ‖db‖ ≤ B)
    (hpow : ‖b ^ k‖ ≤ E) (hprev : ‖b ^ (k - 1)‖ ≤ E) :
    ‖da * b ^ k + a * ((k : ℂ) * b ^ (k - 1) * db)‖ ≤
      A * (1 + (k : ℝ) * B) * E := by
  have hinner : (k : ℝ) * ‖b ^ (k - 1)‖ * ‖db‖ ≤ (k : ℝ) * E * B :=
    mul_le_mul (mul_le_mul_of_nonneg_left hprev (Nat.cast_nonneg k)) hdb
      (norm_nonneg db) (mul_nonneg (Nat.cast_nonneg k) hE)
  calc
    ‖da * b ^ k + a * ((k : ℂ) * b ^ (k - 1) * db)‖ ≤
        ‖da * b ^ k‖ + ‖a * ((k : ℂ) * b ^ (k - 1) * db)‖ := norm_add_le _ _
    _ = ‖da‖ * ‖b ^ k‖ + ‖a‖ * ((k : ℝ) * ‖b ^ (k - 1)‖ * ‖db‖) := by
      simp only [norm_mul, Complex.norm_natCast]
    _ ≤ A * E + A * ((k : ℝ) * E * B) :=
      add_le_add (mul_le_mul hda hpow (norm_nonneg _) hA)
        (mul_le_mul ha hinner (by positivity) hA)
    _ = A * (1 + (k : ℝ) * B) * E := by ring

/-- Manuscript (11)'s value and first-derivative estimates for the concrete
finite expression. Every coefficient and decay bound is discharged from
the constructed roots; the constants depend only on m. -/
theorem boundaryErrorExpression_exp_bounds (m : ℕ) (hm : 2 ≤ m) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ n : ℕ, ∀ theta : ℝ, 0 ≤ theta → theta ≤ Real.pi →
        ‖boundaryErrorExpression m n hm theta‖ ≤
          C * Real.exp (-c * (n : ℝ) * theta) ∧
        ‖deriv (boundaryErrorExpression m n hm) theta‖ ≤
          C * (n + 1 : ℝ) * Real.exp (-c * (n : ℝ) * theta) := by
  classical
  obtain ⟨A, hA, hboundA⟩ := normalizedErrorCoefficient_uniform_bound m hm
  obtain ⟨B, hB, hboundB⟩ := boundaryProductRatio_deriv_uniform_bound m hm
  obtain ⟨c, hc, hdecay⟩ := boundaryProductRatio_uniform_exp_decay m hm
  let M : ℝ := Fintype.card (BoundaryNonleadingSubset m hm)
  let V : ℝ := M * A
  let D : ℝ := M * (A * (1 + (m : ℝ) * B))
  let C : ℝ := max (max V D) 1
  have hVC : V ≤ C := (le_max_left V D).trans (le_max_left _ _)
  have hDC : D ≤ C := (le_max_right V D).trans (le_max_left _ _)
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨c, C, hc, hC, ?_⟩
  intro n theta htheta hthetaPi
  let E : ℝ := Real.exp (-c * (n : ℝ) * theta)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hpoint : theta ∈ Set.Icc (0 : ℝ) Real.pi := ⟨htheta, hthetaPi⟩
  have hterms : ∀ s : BoundaryNonleadingSubset m hm,
      ‖boundaryErrorTerm m n hm s theta‖ ≤ A * E ∧
      ‖deriv (boundaryErrorTerm m n hm s) theta‖ ≤
        (A * (1 + (m : ℝ) * B)) * (n + 1 : ℝ) * E := by
    intro s
    let a : ℝ → ℂ := normalizedErrorCoefficient m (by omega) s.val s.property.1
    let b : ℝ → ℂ := fun t => boundaryProductRatio m t s.val
    have ha : ‖a theta‖ ≤ A := (hboundA s.val s.property.1 theta hpoint).1
    have hda : ‖deriv a theta‖ ≤ A := (hboundA s.val s.property.1 theta hpoint).2
    have hdb : ‖deriv b theta‖ ≤ B := hboundB s theta hpoint
    have hb : ‖b theta‖ ≤ Real.exp (-c * theta) :=
      hdecay s.val s.property.1 s.property.2.1 s.property.2.2 theta htheta hthetaPi
    have hpow : ‖b theta ^ (n + m)‖ ≤ E :=
      norm_pow_le_exp_of_le (b theta) c theta hc.le htheta hb n (n + m) (by omega)
    have hprev : ‖b theta ^ (n + m - 1)‖ ≤ E :=
      norm_pow_le_exp_of_le (b theta) c theta hc.le htheta hb n (n + m - 1) (by omega)
    have hdiffa : DifferentiableAt ℝ a theta :=
      (normalizedErrorCoefficient_contDiffAt m hm s.val s.property.1 theta hpoint).differentiableAt
        (by simp)
    have hdiffb : DifferentiableAt ℝ b theta :=
      (boundaryProductRatio_contDiff m hm s.val).contDiffAt.differentiableAt (by simp)
    have hderiv : deriv (boundaryErrorTerm m n hm s) theta =
        deriv a theta * b theta ^ (n + m) +
          a theta * (((n + m : ℕ) : ℂ) * b theta ^ (n + m - 1) * deriv b theta) := by
      change deriv (fun t => a t * b t ^ (n + m)) theta = _
      convert! (hdiffa.hasDerivAt.mul (hdiffb.hasDerivAt.pow (n + m))).deriv using 1
    have hnmNat : n + m ≤ m * (n + 1) := by
      nlinarith [Nat.mul_le_mul_left n (show 1 ≤ m by omega)]
    have hnm : ((n + m : ℕ) : ℝ) ≤ (m : ℝ) * (n + 1 : ℝ) := by
      exact_mod_cast hnmNat
    have hcoef : 1 + ((n + m : ℕ) : ℝ) * B ≤
        (1 + (m : ℝ) * B) * (n + 1 : ℝ) := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith [mul_le_mul_of_nonneg_right hnm hB.le]
    constructor
    · change ‖a theta * b theta ^ (n + m)‖ ≤ A * E
      rw [norm_mul]
      exact mul_le_mul ha hpow (norm_nonneg _) hA.le
    · rw [hderiv]
      calc
        ‖deriv a theta * b theta ^ (n + m) +
            a theta * (((n + m : ℕ) : ℂ) * b theta ^ (n + m - 1) * deriv b theta)‖ ≤
            A * (1 + ((n + m : ℕ) : ℝ) * B) * E :=
          norm_product_power_derivative_le (a theta) (deriv a theta) (b theta)
            (deriv b theta) (n + m) A B E hA.le hE ha hda hdb hpow hprev
        _ ≤ (A * ((1 + (m : ℝ) * B) * (n + 1 : ℝ))) * E :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef hA.le) hE
        _ = (A * (1 + (m : ℝ) * B)) * (n + 1 : ℝ) * E := by ring
  constructor
  · calc
      ‖boundaryErrorExpression m n hm theta‖ ≤
          ∑ s : BoundaryNonleadingSubset m hm, ‖boundaryErrorTerm m n hm s theta‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _s : BoundaryNonleadingSubset m hm, A * E :=
        Finset.sum_le_sum (fun s _ => (hterms s).1)
      _ = V * E := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        dsimp [V, M]
        ring
      _ ≤ C * E := mul_le_mul_of_nonneg_right hVC hE
  · have hderivSum : deriv (boundaryErrorExpression m n hm) theta =
        ∑ s : BoundaryNonleadingSubset m hm, deriv (boundaryErrorTerm m n hm s) theta := by
      unfold boundaryErrorExpression
      exact deriv_fun_sum (fun s _ =>
        (boundaryErrorTerm_contDiffAt m n hm s theta hpoint).differentiableAt (by simp))
    rw [hderivSum]
    calc
      ‖∑ s : BoundaryNonleadingSubset m hm, deriv (boundaryErrorTerm m n hm s) theta‖ ≤
          ∑ s : BoundaryNonleadingSubset m hm, ‖deriv (boundaryErrorTerm m n hm s) theta‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _s : BoundaryNonleadingSubset m hm,
          (A * (1 + (m : ℝ) * B)) * (n + 1 : ℝ) * E :=
        Finset.sum_le_sum (fun s _ => (hterms s).2)
      _ = D * (n + 1 : ℝ) * E := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        dsimp [D, M]
        ring
      _ ≤ C * (n + 1 : ℝ) * E :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hDC (by positivity)) hE

#print axioms boundaryErrorTerm_contDiffAt
#print axioms boundaryErrorExpression_contDiffAt
#print axioms boundaryProductRatio_deriv_uniform_bound
#print axioms boundaryErrorExpression_exp_bounds

end MF21Restart
