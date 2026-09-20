import MF21.BulkEndpoint
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The complete, distinct characteristic-root family for MF-21 at
interior angles. It is built from the actual stable roots, not assumed. -/

noncomputable section
open scoped Topology ContDiff
namespace MF21Bulk

def omega (m : ℕ) (j : Fin m) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / m) ^ (j : ℕ)

theorem omega_norm (m : ℕ) (j : Fin m) : ‖omega m j‖ = 1 := by
  rw [omega, norm_pow]
  have he : (2 * Real.pi * Complex.I / (m : ℂ)) =
      ((2 * Real.pi / m : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [he, Complex.norm_exp_ofReal_mul_I, one_pow]

theorem omega_pow (m : ℕ) (hm : 0 < m) (j : Fin m) : (omega m j) ^ m = 1 := by
  rw [omega, ← pow_mul, Nat.mul_comm, pow_mul,
    (Complex.isPrimitiveRoot_exp m (ne_of_gt hm)).pow_eq_one, one_pow]

theorem omega_injective (m : ℕ) (hm : 0 < m) : Function.Injective (omega m) := by
  intro i j hij
  exact Fin.ext ((Complex.isPrimitiveRoot_exp m (ne_of_gt hm)).pow_inj i.isLt j.isLt hij)

theorem omega_ne_one (m : ℕ) (hm : 0 < m) (j : Fin m) (hj : j.val ≠ 0) :
    omega m j ≠ 1 :=
  (Complex.isPrimitiveRoot_exp m (ne_of_gt hm)).pow_ne_one_of_pos_of_lt hj j.isLt

theorem omega_eq_exp (m : ℕ) (j : Fin m) :
    omega m j =
      Complex.exp (((2 * Real.pi * j.val / m : ℝ) : ℂ) * Complex.I) := by
  rw [omega, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

def kappa (m : ℕ) (j : Fin m) : ℂ :=
  Complex.exp (((Real.pi * j.val / m - Real.pi / 2 : ℝ) : ℂ) * Complex.I)

theorem kappa_sq (m : ℕ) (j : Fin m) : kappa m j ^ 2 = -omega m j := by
  rw [kappa, ← Complex.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have he : (2 : ℂ) * (((Real.pi * j.val / m - Real.pi / 2 : ℝ) : ℂ) * Complex.I) =
      (((2 * Real.pi * j.val / m : ℝ) : ℂ) * Complex.I) - (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_sub, Complex.exp_pi_mul_I, omega_eq_exp]
  simp only [div_neg, div_one]

theorem kappa_re_pos (m : ℕ) (hm : 0 < m) (j : Fin m) (hj : j.val ≠ 0) :
    0 < (kappa m j).re := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hjR : (0 : ℝ) < j.val := by exact_mod_cast Nat.pos_of_ne_zero hj
  have hjm : (j.val : ℝ) < m := by exact_mod_cast j.isLt
  have hlo : 0 < Real.pi * j.val / m := div_pos (mul_pos Real.pi_pos hjR) hmR
  have hhi : Real.pi * j.val / m < Real.pi :=
    (div_lt_iff₀ hmR).2 (mul_lt_mul_of_pos_left hjm Real.pi_pos)
  simp only [kappa, Complex.exp_mul_I, Complex.add_re, Complex.mul_re,
    Complex.I_re, mul_zero, Complex.sin_ofReal_im, Complex.I_im, zero_mul,
    sub_self, add_zero, Complex.cos_ofReal_re]
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith

theorem omega_stableRoot_endpoint_extension (m : ℕ) (hm : 0 < m)
    (j : Fin m) (hj : j.val ≠ 0) :
    ∃ R : ℝ → ℂ, R 0 = 1 ∧ ContDiffAt ℝ ∞ R 0 ∧
      HasDerivAt R (-kappa m j) 0 ∧
      ∀ᶠ t : ℝ in 𝓝[>] 0, R t = stableRoot (omega m j) (t ^ 2) :=
  stableRoot_endpoint_extension (omega m j) (kappa m j) (omega_norm m j)
    (omega_ne_one m hm j hj) (kappa_sq m j) (kappa_re_pos m hm j hj)

def spectralBase (theta : ℝ) : ℝ := (2 * Real.sin (theta / 2)) ^ 2

theorem spectralBase_eq (theta : ℝ) : spectralBase theta = 2 - 2 * Real.cos theta := by
  have hc := Real.cos_two_mul (theta / 2)
  have ht := Real.sin_sq_add_cos_sq (theta / 2)
  rw [show 2 * (theta / 2) = theta by ring] at hc
  dsimp [spectralBase]
  nlinarith

theorem spectralBase_pos (theta : ℝ) (ht : 0 < theta) (htp : theta < Real.pi) :
    0 < spectralBase theta := by
  apply sq_pos_of_pos
  exact mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))

def unitRoot (theta : ℝ) : ℂ := Complex.exp ((theta : ℂ) * Complex.I)

theorem unitRoot_norm (theta : ℝ) : ‖unitRoot theta‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I theta

theorem unitRoot_ne_zero (theta : ℝ) : unitRoot theta ≠ 0 := Complex.exp_ne_zero _

theorem unitRoot_characteristic (theta : ℝ) :
    2 - unitRoot theta - (unitRoot theta)⁻¹ = (spectralBase theta : ℂ) := by
  rw [Complex.inv_eq_conj (unitRoot_norm theta), spectralBase_eq]
  apply Complex.ext <;> simp [unitRoot, Complex.exp_mul_I, Complex.mul_re, Complex.mul_im] <;> ring

theorem unitRoot_ne_inv (theta : ℝ) (ht : 0 < theta) (htp : theta < Real.pi) :
    unitRoot theta ≠ (unitRoot theta)⁻¹ := by
  rw [Complex.inv_eq_conj (unitRoot_norm theta)]
  intro he
  have hi := congrArg Complex.im he
  have hs := Real.sin_pos_of_pos_of_lt_pi ht htp
  simp [unitRoot, Complex.exp_mul_I, Complex.mul_im, ← Complex.ofReal_sin] at hi
  linarith

/-- One root from each reciprocal pair, choosing the positive-angle unit
root for omega = 1 and the stable root for all other roots of unity. -/
def baseRoot (m : ℕ) (theta : ℝ) (j : Fin m) : ℂ :=
  if j.val = 0 then unitRoot theta else stableRoot (omega m j) (spectralBase theta)

theorem baseRoot_spec (m : ℕ) (hm : 0 < m) (theta : ℝ)
    (ht : 0 < theta) (htp : theta < Real.pi) (j : Fin m) :
    baseRoot m theta j ≠ 0 ∧
    2 - baseRoot m theta j - (baseRoot m theta j)⁻¹ =
      omega m j * (spectralBase theta : ℂ) := by
  by_cases hj : j.val = 0
  · simp only [baseRoot, if_pos hj, omega, hj, pow_zero, one_mul]
    exact ⟨unitRoot_ne_zero theta, unitRoot_characteristic theta⟩
  · obtain ⟨hn, _, he⟩ := stableRoot_spec (omega m j) (spectralBase theta)
      (spectralBase_pos theta ht htp) (omega_norm m j) (omega_ne_one m hm j hj)
    simpa only [baseRoot, if_neg hj] using And.intro hn he

theorem baseRoot_injective (m : ℕ) (hm : 0 < m) (theta : ℝ)
    (ht : 0 < theta) (htp : theta < Real.pi) :
    Function.Injective (baseRoot m theta) := by
  intro i j hij
  apply omega_injective m hm
  have hi := (baseRoot_spec m hm theta ht htp i).2
  have hj := (baseRoot_spec m hm theta ht htp j).2
  rw [hij] at hi
  exact mul_right_cancel₀ (by exact_mod_cast ne_of_gt (spectralBase_pos theta ht htp))
    (hi.symm.trans hj)

theorem baseRoot_ne_inv (m : ℕ) (hm : 0 < m) (theta : ℝ)
    (ht : 0 < theta) (htp : theta < Real.pi) (j : Fin m) :
    baseRoot m theta j ≠ (baseRoot m theta j)⁻¹ := by
  by_cases hj : j.val = 0
  · simpa only [baseRoot, if_pos hj] using unitRoot_ne_inv theta ht htp
  · have hn := (stableRoot_spec (omega m j) (spectralBase theta)
      (spectralBase_pos theta ht htp) (omega_norm m j) (omega_ne_one m hm j hj)).2.1
    have hz := (baseRoot_spec m hm theta ht htp j).1
    intro he
    have heq : baseRoot m theta j * baseRoot m theta j = 1 := by
      calc
        _ = baseRoot m theta j * (baseRoot m theta j)⁻¹ := by rw [← he]
        _ = 1 := mul_inv_cancel₀ hz
    have hh := congrArg norm heq
    rw [norm_mul, norm_one] at hh
    simp only [baseRoot, if_neg hj] at hh
    nlinarith [norm_nonneg (stableRoot (omega m j) (spectralBase theta))]

theorem baseRoot_ne_other_inv (m : ℕ) (hm : 0 < m) (theta : ℝ)
    (ht : 0 < theta) (htp : theta < Real.pi) (i j : Fin m) :
    baseRoot m theta i ≠ (baseRoot m theta j)⁻¹ := by
  intro he
  have hi := (baseRoot_spec m hm theta ht htp i).2
  have hj := (baseRoot_spec m hm theta ht htp j).2
  have heomega : omega m i = omega m j := by
    have hprod : omega m i * (spectralBase theta : ℂ) =
        omega m j * (spectralBase theta : ℂ) := by
      rw [he, inv_inv] at hi
      linear_combination -hi + hj
    exact mul_right_cancel₀
      (by exact_mod_cast ne_of_gt (spectralBase_pos theta ht htp)) hprod
  have hij : i = j := omega_injective m hm heomega
  subst j
  exact baseRoot_ne_inv m hm theta ht htp i he

/-- All 2m characteristic roots, indexed first by the m chosen roots and
then by their reciprocals. Reordering this family only changes a boundary
determinant by a sign. -/
def characteristicRoots (m : ℕ) (theta : ℝ) : Fin (m + m) → ℂ :=
  Fin.addCases (baseRoot m theta) (fun j => (baseRoot m theta j)⁻¹)

theorem characteristicRoots_injective (m : ℕ) (hm : 0 < m) (theta : ℝ)
    (ht : 0 < theta) (htp : theta < Real.pi) :
    Function.Injective (characteristicRoots m theta) := by
  intro i j
  induction i using Fin.addCases <;> induction j using Fin.addCases <;>
    simp only [characteristicRoots, Fin.addCases_left, Fin.addCases_right]
  · intro he
    exact congrArg (Fin.castAdd m) (baseRoot_injective m hm theta ht htp he)
  · intro he
    exact False.elim (baseRoot_ne_other_inv m hm theta ht htp _ _ he)
  · intro he
    exact False.elim (baseRoot_ne_other_inv m hm theta ht htp _ _ he.symm)
  · intro he
    exact congrArg (Fin.natAdd m)
      (baseRoot_injective m hm theta ht htp (inv_injective he))

theorem characteristicRoots_spec (m : ℕ) (hm : 0 < m) (theta : ℝ)
    (ht : 0 < theta) (htp : theta < Real.pi) (j : Fin (m + m)) :
    characteristicRoots m theta j ≠ 0 ∧
      (2 - characteristicRoots m theta j - (characteristicRoots m theta j)⁻¹) ^ m =
        (spectralBase theta : ℂ) ^ m := by
  have hb (i : Fin m) :
      (2 - baseRoot m theta i - (baseRoot m theta i)⁻¹) ^ m =
        (spectralBase theta : ℂ) ^ m := by
    rw [(baseRoot_spec m hm theta ht htp i).2, mul_pow, omega_pow m hm i, one_mul]
  induction j using Fin.addCases <;>
    simp only [characteristicRoots, Fin.addCases_left, Fin.addCases_right]
  · exact ⟨(baseRoot_spec m hm theta ht htp _).1, hb _⟩
  · refine ⟨inv_ne_zero (baseRoot_spec m hm theta ht htp _).1, ?_⟩
    rw [inv_inv, sub_sub, add_comm, ← sub_sub]
    exact hb _

end MF21Bulk

#print axioms MF21Bulk.characteristicRoots_injective
#print axioms MF21Bulk.characteristicRoots_spec
#print axioms MF21Bulk.omega_stableRoot_endpoint_extension
