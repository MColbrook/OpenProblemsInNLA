import MF21.BulkTotalPhase
import MF21.BulkSlopes
import Mathlib.LinearAlgebra.Vandermonde

noncomputable section
open scoped BigOperators
namespace MF21Bulk

theorem unitRoot_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    unitRoot (∑ i ∈ s, f i) = ∏ i ∈ s, unitRoot (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [unitRoot]
  | @insert a s ha ih => simp [ha, unitRoot_add, ih]

def phaseProduct (m : ℕ) (theta : ℝ) : ℂ :=
  ∏ j : Fin (m - 1), phaseFactor (omega m (nontrivialIndex m j)) theta

theorem phaseProduct_polar (m : ℕ) (theta : ℝ) :
    phaseProduct m theta =
      (∏ j : Fin (m - 1), (‖phaseFactor (omega m (nontrivialIndex m j)) theta‖ : ℂ)) *
        unitRoot (psi m theta) := by
  rw [psi, unitRoot_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  exact (Complex.norm_mul_exp_arg_mul_I _).symm

theorem vandermonde_head (k : ℕ) (v : Fin (k + 1) → ℂ) :
    (Matrix.vandermonde v).det =
      (∏ j : Fin k, (v j.succ - v 0)) *
        (Matrix.vandermonde (fun j : Fin k => v j.succ)).det := by
  rw [Matrix.det_vandermonde, Fin.prod_univ_succ, Fin.prod_Ioi_zero]
  simp only [Fin.prod_Ioi_succ, Matrix.det_vandermonde]

theorem vandermonde_cons_head (k : ℕ) (z : ℂ) (r : Fin k → ℂ) :
    (Matrix.vandermonde (Fin.cons z r)).det =
      (∏ j : Fin k, (r j - z)) * (Matrix.vandermonde r).det := by
  simpa using vandermonde_head k (Fin.cons z r)

def pairCoefficient (k : ℕ) (z : ℂ) (r : Fin k → ℂ) : ℂ :=
  (Matrix.vandermonde (Fin.cons z r)).det *
    (Matrix.vandermonde (Fin.cons z⁻¹ (fun j => (r j)⁻¹))).det

theorem pairCoefficient_factor (k : ℕ) (z : ℂ) (r : Fin k → ℂ)
    (hz : z ≠ 0) (hr : ∀ j, r j ≠ 0) :
    pairCoefficient k z r =
      (Matrix.vandermonde r).det *
      (Matrix.vandermonde (fun j => (r j)⁻¹)).det *
      (∏ j, (r j)⁻¹) * (-z) ^ k * (∏ j, (1 - r j * z⁻¹)) ^ 2 := by
  rw [pairCoefficient, vandermonde_cons_head, vandermonde_cons_head]
  have he (j : Fin k) : r j - z = (-z) * (1 - r j * z⁻¹) := by
    field_simp
    ring
  have hi (j : Fin k) : (r j)⁻¹ - z⁻¹ = (r j)⁻¹ * (1 - r j * z⁻¹) := by
    field_simp [hr j]
  simp only [he, hi]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

theorem pairCoefficient_swap_relation (k : ℕ) (z : ℂ) (r : Fin k → ℂ)
    (hz : z ≠ 0) (hr : ∀ j, r j ≠ 0) :
    pairCoefficient k z⁻¹ r * z ^ (2 * k) * (∏ j, (1 - r j * z⁻¹)) ^ 2 =
      pairCoefficient k z r * (∏ j, (1 - r j * z)) ^ 2 := by
  rw [pairCoefficient_factor k z r hz hr,
    pairCoefficient_factor k z⁻¹ r (inv_ne_zero hz) hr, inv_inv]
  have hp : (-z⁻¹) ^ k * z ^ (2 * k) = (-z) ^ k := by
    rw [pow_mul, ← mul_pow]
    congr 1
    field_simp
  linear_combination
    (Matrix.vandermonde r).det *
      (Matrix.vandermonde (fun j => (r j)⁻¹)).det *
      (∏ j, (r j)⁻¹) *
      (∏ j, (1 - r j * z)) ^ 2 * (∏ j, (1 - r j * z⁻¹)) ^ 2 * hp

theorem conjugate_factor_product (k : ℕ) (z : ℂ) (r : Fin k → ℂ)
    (hz : ‖z‖ = 1) (sigma : Equiv.Perm (Fin k))
    (hr : ∀ j, (starRingEnd ℂ) (r j) = r (sigma j)) :
    (starRingEnd ℂ) (∏ j, (1 - r j * z⁻¹)) = ∏ j, (1 - r j * z) := by
  rw [map_prod]
  have he : (starRingEnd ℂ) z⁻¹ = z := by
    rw [map_inv₀, ← Complex.inv_eq_conj hz, inv_inv]
  simp only [map_sub, map_one, map_mul, hr, he]
  exact Equiv.prod_comp sigma (fun j => 1 - r j * z)

theorem unitRoot_nat_mul (theta : ℝ) (k : ℕ) :
    unitRoot theta ^ k = unitRoot (k * theta) := by
  rw [unitRoot, unitRoot, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem unitRoot_conj (theta : ℝ) :
    (starRingEnd ℂ) (unitRoot theta) = unitRoot (-theta) := by
  rw [← Complex.inv_eq_conj (unitRoot_norm theta), unitRoot_neg]

theorem polar_conjugate (f : ℂ) (rho psi : ℝ)
    (hf : f = (rho : ℂ) * unitRoot psi) :
    (starRingEnd ℂ) f = f * unitRoot (-2 * psi) := by
  rw [hf, map_mul, Complex.conj_ofReal, unitRoot_conj]
  have he : unitRoot psi * unitRoot (-2 * psi) = unitRoot (-psi) := by
    rw [← unitRoot_add]
    congr 1
    ring
  linear_combination -(rho : ℂ) * he

theorem pairCoefficient_swap_phase (k : ℕ) (theta : ℝ) (r : Fin k → ℂ)
    (hr : ∀ j, r j ≠ 0) (rho psi : ℝ) (hrho : rho ≠ 0)
    (hpolar : (∏ j, (1 - r j * (unitRoot theta)⁻¹)) = (rho : ℂ) * unitRoot psi)
    (hconj : (∏ j, (1 - r j * unitRoot theta)) =
      (starRingEnd ℂ) (∏ j, (1 - r j * (unitRoot theta)⁻¹))) :
    pairCoefficient k (unitRoot theta)⁻¹ r =
      pairCoefficient k (unitRoot theta) r * unitRoot (-2 * k * theta - 4 * psi) := by
  let f : ℂ := ∏ j, (1 - r j * (unitRoot theta)⁻¹)
  have hf : f ≠ 0 := by
    rw [show f = (rho : ℂ) * unitRoot psi from hpolar]
    exact mul_ne_zero (by exact_mod_cast hrho) (unitRoot_ne_zero psi)
  have hfc : (∏ j, (1 - r j * unitRoot theta)) = f * unitRoot (-2 * psi) := by
    rw [hconj]
    exact polar_conjugate f rho psi hpolar
  have hphase : unitRoot (-2 * k * theta - 4 * psi) * unitRoot theta ^ (2 * k) =
      unitRoot (-2 * psi) ^ 2 := by
    rw [unitRoot_nat_mul, unitRoot_nat_mul, ← unitRoot_add]
    congr 1
    push_cast
    ring
  apply mul_right_cancel₀ (mul_ne_zero
    (pow_ne_zero (2 * k) (unitRoot_ne_zero theta)) (pow_ne_zero 2 hf))
  have he := pairCoefficient_swap_relation k (unitRoot theta) r (unitRoot_ne_zero theta) hr
  rw [hfc] at he
  change pairCoefficient k (unitRoot theta)⁻¹ r * (unitRoot theta ^ (2 * k) * f ^ 2) =
    (pairCoefficient k (unitRoot theta) r * unitRoot (-2 * k * theta - 4 * psi)) *
      (unitRoot theta ^ (2 * k) * f ^ 2)
  dsimp only [f] at *
  linear_combination he -
    pairCoefficient k (unitRoot theta) r * f ^ 2 * hphase

def stableTail (m : ℕ) (theta : ℝ) (j : Fin (m - 1)) : ℂ :=
  stableRoot (omega m (nontrivialIndex m j)) (spectralBase theta)

theorem stableTail_conj (m : ℕ) (hm : 0 < m) (theta : ℝ)
    (hs : 0 < spectralBase theta) (j : Fin (m - 1)) :
    (starRingEnd ℂ) (stableTail m theta j) = stableTail m theta j.rev := by
  rw [stableTail, ← stableRoot_conj _ _ hs (omega_norm m (nontrivialIndex m j))
    (omega_ne_one m hm _ (nontrivialIndex_ne_zero m j))]
  rw [← omega_nontrivial_rev m hm j]
  rfl

theorem stableTail_ne_zero (m : ℕ) (hm : 0 < m) (theta : ℝ)
    (hs : 0 < spectralBase theta) (j : Fin (m - 1)) : stableTail m theta j ≠ 0 :=
  (stableRoot_spec _ _ hs (omega_norm m (nontrivialIndex m j))
    (omega_ne_one m hm _ (nontrivialIndex_ne_zero m j))).1

theorem vandermonde_conj_permute (k : ℕ) (r : Fin k → ℂ)
    (sigma : Equiv.Perm (Fin k))
    (hr : ∀ j, (starRingEnd ℂ) (r j) = r (sigma j)) :
    (starRingEnd ℂ) (Matrix.vandermonde r).det =
      (Equiv.Perm.sign sigma : ℤ) * (Matrix.vandermonde r).det := by
  rw [RingHom.map_det]
  have he : (starRingEnd ℂ).mapMatrix (Matrix.vandermonde r) =
      (Matrix.vandermonde r).submatrix sigma id := by
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.vandermonde, hr]
  rw [he, Matrix.det_permute]

def tailCore (k : ℕ) (r : Fin k → ℂ) : ℂ :=
  (Matrix.vandermonde r).det *
    (Matrix.vandermonde (fun j => (r j)⁻¹)).det * (∏ j, (r j)⁻¹)

theorem tailCore_conj (k : ℕ) (r : Fin k → ℂ) (sigma : Equiv.Perm (Fin k))
    (hr : ∀ j, (starRingEnd ℂ) (r j) = r (sigma j)) :
    (starRingEnd ℂ) (tailCore k r) = tailCore k r := by
  have hri (j : Fin k) : (starRingEnd ℂ) (r j)⁻¹ = (r (sigma j))⁻¹ := by
    rw [map_inv₀, hr]
  have hprod : (starRingEnd ℂ) (∏ j, (r j)⁻¹) = ∏ j, (r j)⁻¹ := by
    rw [map_prod]
    simp only [hri]
    exact Equiv.prod_comp sigma (fun j => (r j)⁻¹)
  have hsign : ((Equiv.Perm.sign sigma : ℤ) : ℂ) *
      ((Equiv.Perm.sign sigma : ℤ) : ℂ) = 1 := by
    have he := congrArg (fun u : ℤˣ => ((u : ℤ) : ℂ))
      (Int.units_mul_self (Equiv.Perm.sign sigma))
    simpa only [Units.val_mul, Int.cast_mul, Units.val_one, Int.cast_one] using he
  rw [tailCore, map_mul, map_mul, hprod,
    vandermonde_conj_permute k r sigma hr,
    vandermonde_conj_permute k (fun j => (r j)⁻¹) sigma hri]
  linear_combination
    (Matrix.vandermonde r).det *
      (Matrix.vandermonde (fun j => (r j)⁻¹)).det * (∏ j, (r j)⁻¹) * hsign

theorem pairCoefficient_conj (k : ℕ) (z : ℂ) (r : Fin k → ℂ)
    (hz : ‖z‖ = 1) (hrn : ∀ j, r j ≠ 0) (sigma : Equiv.Perm (Fin k))
    (hr : ∀ j, (starRingEnd ℂ) (r j) = r (sigma j)) :
    (starRingEnd ℂ) (pairCoefficient k z r) = pairCoefficient k z⁻¹ r := by
  have hzn : z ≠ 0 := by intro h; simp [h] at hz
  have hf : pairCoefficient k z r =
      tailCore k r * (-z)^k * (∏ j, (1-r j*z⁻¹))^2 :=
    pairCoefficient_factor k z r hzn hrn
  have hfi : pairCoefficient k z⁻¹ r =
      tailCore k r * (-z⁻¹)^k * (∏ j, (1-r j*z))^2 := by
    simpa only [tailCore, inv_inv] using pairCoefficient_factor k z⁻¹ r (inv_ne_zero hzn) hrn
  rw [hf, hfi, map_mul, map_mul, map_pow, map_pow, map_neg,
    tailCore_conj k r sigma hr, ← Complex.inv_eq_conj hz,
    conjugate_factor_product k z r hz sigma hr]

theorem actual_pairCoefficient_swap_phase (m : ℕ) (hm : 0 < m) (theta : ℝ)
    (hs : 0 < spectralBase theta) :
    pairCoefficient (m - 1) (unitRoot theta)⁻¹ (stableTail m theta) =
      pairCoefficient (m - 1) (unitRoot theta) (stableTail m theta) *
        unitRoot (-2 * (m - 1 : ℕ) * theta - 4 * psi m theta) := by
  let rho : ℝ := ∏ j : Fin (m - 1),
    ‖phaseFactor (omega m (nontrivialIndex m j)) theta‖
  have hn (j : Fin (m - 1)) :
      phaseFactor (omega m (nontrivialIndex m j)) theta ≠ 0 := by
    have hp := phaseFactor_re_pos _ theta hs (omega_norm m (nontrivialIndex m j))
      (omega_ne_one m hm _ (nontrivialIndex_ne_zero m j))
    intro h
    simp [h] at hp
  have hrho : rho ≠ 0 := by
    exact ne_of_gt (Finset.prod_pos fun j _ => norm_pos_iff.mpr (hn j))
  apply pairCoefficient_swap_phase (m - 1) theta (stableTail m theta)
    (stableTail_ne_zero m hm theta hs) rho (psi m theta) hrho
  · have hp := phaseProduct_polar m theta
    dsimp only [rho]
    push_cast
    exact hp
  · exact (conjugate_factor_product (m - 1) (unitRoot theta) (stableTail m theta)
      (unitRoot_norm theta) Fin.revPerm (stableTail_conj m hm theta hs)).symm

def tailInverseProduct (m : ℕ) (theta : ℝ) : ℂ :=
  ∏ j : Fin (m - 1), (stableTail m theta j)⁻¹

def rootLeadingAmplitude (m n : ℕ) (theta : ℝ) : ℂ :=
  pairCoefficient (m - 1) (unitRoot theta) (stableTail m theta) *
    ((unitRoot theta)⁻¹ * tailInverseProduct m theta) ^ (n + m)

def secularPhase (m n : ℕ) (theta : ℝ) : ℝ :=
  (n + 1 : ℝ) * theta - 2 * psi m theta

theorem baseRoot_cons (k : ℕ) (theta : ℝ) :
    baseRoot (k + 1) theta = Fin.cons (unitRoot theta) (stableTail (k + 1) theta) := by
  funext j
  induction j using Fin.cases with
  | zero => simp [baseRoot]
  | succ j =>
    simp only [baseRoot, Fin.val_succ, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      ↓reduceIte, Fin.cons_succ, stableTail]
    congr 2

theorem baseRoot_inverse_cons (k : ℕ) (theta : ℝ) :
    (fun j => (baseRoot (k + 1) theta j)⁻¹) =
      Fin.cons (unitRoot theta)⁻¹ (fun j => (stableTail (k + 1) theta j)⁻¹) := by
  rw [baseRoot_cons]
  funext j
  induction j using Fin.cases <;> simp

theorem root_coefficient_eq_pair (m : ℕ) (hm : 0 < m) (theta : ℝ) :
    (Matrix.vandermonde (baseRoot m theta)).det *
      (Matrix.vandermonde (fun j => (baseRoot m theta j)⁻¹)).det =
        pairCoefficient (m - 1) (unitRoot theta) (stableTail m theta) := by
  cases m with
  | zero => omega
  | succ k =>
    rw [baseRoot_inverse_cons, baseRoot_cons]
    rfl

theorem root_inverse_product_eq (m : ℕ) (hm : 0 < m) (theta : ℝ) :
    (∏ j : Fin m, (baseRoot m theta j)⁻¹) =
      (unitRoot theta)⁻¹ * tailInverseProduct m theta := by
  cases m with
  | zero => omega
  | succ k =>
    rw [baseRoot_inverse_cons]
    change (∏ j : Fin (k + 1), Fin.cons (unitRoot theta)⁻¹
      (fun j => (stableTail (k + 1) theta j)⁻¹) j) = _
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rfl

theorem actual_swapped_leading_phase (m n : ℕ) (hm : 0 < m) (theta : ℝ)
    (hs : 0 < spectralBase theta) :
    pairCoefficient (m - 1) (unitRoot theta)⁻¹ (stableTail m theta) *
      (unitRoot theta * tailInverseProduct m theta) ^ (n + m) =
        rootLeadingAmplitude m n theta * unitRoot (2 * secularPhase m n theta) := by
  rw [actual_pairCoefficient_swap_phase m hm theta hs]
  have he :
      unitRoot (-2 * (m - 1 : ℕ) * theta - 4 * psi m theta) * unitRoot theta ^ (n + m) =
      ((unitRoot theta)⁻¹) ^ (n + m) * unitRoot (2 * secularPhase m n theta) := by
    rw [← unitRoot_neg, unitRoot_nat_mul, unitRoot_nat_mul, ← unitRoot_add, ← unitRoot_add]
    congr 1
    dsimp [secularPhase]
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    ring
  dsimp only [rootLeadingAmplitude]
  rw [mul_pow, mul_pow]
  linear_combination
    pairCoefficient (m - 1) (unitRoot theta) (stableTail m theta) *
      tailInverseProduct m theta ^ (n + m) * he

theorem rootLeadingAmplitude_conj (m n : ℕ) (hm : 0 < m) (theta : ℝ)
    (hs : 0 < spectralBase theta) :
    (starRingEnd ℂ) (rootLeadingAmplitude m n theta) =
      rootLeadingAmplitude m n theta * unitRoot (2 * secularPhase m n theta) := by
  have hQ : (starRingEnd ℂ) (tailInverseProduct m theta) = tailInverseProduct m theta := by
    rw [tailInverseProduct, map_prod]
    simp only [map_inv₀, stableTail_conj m hm theta hs]
    exact Equiv.prod_comp (Fin.revPerm : Equiv.Perm (Fin (m - 1)))
      (fun j => (stableTail m theta j)⁻¹)
  have hzc : (starRingEnd ℂ) (unitRoot theta)⁻¹ = unitRoot theta := by
    rw [map_inv₀, ← Complex.inv_eq_conj (unitRoot_norm theta), inv_inv]
  rw [rootLeadingAmplitude, map_mul, map_pow, map_mul,
    pairCoefficient_conj (m - 1) (unitRoot theta) (stableTail m theta)
      (unitRoot_norm theta) (stableTail_ne_zero m hm theta hs) Fin.revPerm
      (stableTail_conj m hm theta hs), hzc, hQ]
  exact actual_swapped_leading_phase m n hm theta hs

theorem one_sub_unitRoot_two (F : ℝ) :
    1 - unitRoot (2 * F) =
      -2 * Complex.I * unitRoot F * (Real.sin F : ℂ) := by
  have he := unitRoot_factor (2 * F)
  have ht : (2 * F) / 2 = F := by ring
  simp only [halfSine, ht, Complex.ofReal_mul, Complex.ofReal_ofNat] at he
  linear_combination -he

/-- The precise sine normalization once the swapped leading term has
phase ratio exp(2 i F). This keeps the normalization independent of
any assertion about the sign of a product of stable roots. -/
theorem leading_pair_sine (A : ℂ) (F : ℝ) :
    A - A * unitRoot (2 * F) =
      (-2 * Complex.I * A * unitRoot F) * (Real.sin F : ℂ) := by
  linear_combination A * one_sub_unitRoot_two F

theorem actual_leading_pair_sine (m n : ℕ) (hm : 0 < m) (theta : ℝ)
    (hs : 0 < spectralBase theta) :
    rootLeadingAmplitude m n theta -
      pairCoefficient (m - 1) (unitRoot theta)⁻¹ (stableTail m theta) *
        (unitRoot theta * tailInverseProduct m theta) ^ (n + m) =
      (-2 * Complex.I * rootLeadingAmplitude m n theta * unitRoot (secularPhase m n theta)) *
        (Real.sin (secularPhase m n theta) : ℂ) := by
  rw [actual_swapped_leading_phase m n hm theta hs]
  exact leading_pair_sine _ _

theorem sineNormalizer_ne_zero (A : ℂ) (F : ℝ) (hA : A ≠ 0) :
    -2 * Complex.I * A * unitRoot F ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hA)
    (unitRoot_ne_zero F)

/-- Conjugation of the leading terms proves the sine normalizer is
pure imaginary; this is the same conjugation type as the boundary
determinant, so their quotient is real. -/
theorem sineNormalizer_conj (A : ℂ) (F : ℝ)
    (hA : (starRingEnd ℂ) A = A * unitRoot (2 * F)) :
    (starRingEnd ℂ) (-2 * Complex.I * A * unitRoot F) =
      -(-2 * Complex.I * A * unitRoot F) := by
  simp only [map_mul, map_neg, map_ofNat, Complex.conj_I, hA, unitRoot_conj]
  have he : unitRoot (2 * F) * unitRoot (-F) = unitRoot F := by
    rw [← unitRoot_add]
    congr 1
    ring
  linear_combination (2 * Complex.I * A) * he

theorem normalized_boundary_real (D A : ℂ) (F : ℝ)
    (hD : (starRingEnd ℂ) D = -D)
    (hA : (starRingEnd ℂ) A = A * unitRoot (2 * F)) :
    (D / (-2 * Complex.I * A * unitRoot F)).im = 0 := by
  have he : (starRingEnd ℂ) (D / (-2 * Complex.I * A * unitRoot F)) =
      D / (-2 * Complex.I * A * unitRoot F) := by
    rw [map_div₀, hD, sineNormalizer_conj A F hA]
    simp only [neg_div, div_neg, neg_neg]
  have hi := congrArg Complex.im he
  simp only [Complex.conj_im] at hi
  linarith

end MF21Bulk

#print axioms MF21Bulk.phaseProduct_polar
#print axioms MF21Bulk.pairCoefficient_factor
#print axioms MF21Bulk.pairCoefficient_swap_relation
#print axioms MF21Bulk.conjugate_factor_product
#print axioms MF21Bulk.actual_pairCoefficient_swap_phase
#print axioms MF21Bulk.normalized_boundary_real
#print axioms MF21Bulk.actual_leading_pair_sine
#print axioms MF21Bulk.rootLeadingAmplitude_conj
