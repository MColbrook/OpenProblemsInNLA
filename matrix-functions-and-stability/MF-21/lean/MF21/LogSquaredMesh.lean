import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-! An admissible approximating mesh for every point of [0,pi], including
both endpoints, with source indices above ceil(log(n+2)^2). -/

open Filter Asymptotics
open scoped Topology

noncomputable section
namespace MF21Mesh

def denominator (n : ℕ) : ℝ := (n : ℝ) + 2

theorem denominator_pos (n : ℕ) : 0 < denominator n := by
  unfold denominator
  positivity

theorem denominator_atTop : Tendsto denominator atTop atTop :=
  tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop

theorem inv_denominator_tendsto :
    Tendsto (fun n ↦ (denominator n)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp denominator_atTop

def cutoff (n : ℕ) : ℕ := Nat.ceil ((Real.log (denominator n)) ^ 2)

theorem log_squared_ratio_tendsto :
    Tendsto (fun n ↦ (Real.log (denominator n)) ^ 2 / denominator n)
      atTop (𝓝 0) := by
  have H : (fun x : ℝ ↦ (Real.log x) ^ 2) =o[atTop] (fun x ↦ x) := by
    simpa only [Real.rpow_two, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (s := 1) (by norm_num))
  exact (H.comp_tendsto denominator_atTop).tendsto_div_nhds_zero

theorem cutoff_ratio_tendsto :
    Tendsto (fun n ↦ (cutoff n : ℝ) / denominator n) atTop (𝓝 0) := by
  apply squeeze_zero
    (fun n ↦ div_nonneg (Nat.cast_nonneg _) (denominator_pos n).le)
    (g := fun n ↦ (Real.log (denominator n)) ^ 2 / denominator n +
      (denominator n)⁻¹)
  · intro n
    have hc := (Nat.ceil_lt_add_one (sq_nonneg (Real.log (denominator n)))).le
    calc
      (cutoff n : ℝ) / denominator n ≤
          ((Real.log (denominator n)) ^ 2 + 1) / denominator n :=
        div_le_div_of_nonneg_right hc (denominator_pos n).le
      _ = _ := by rw [add_div, one_div]
  · simpa only [add_zero] using log_squared_ratio_tendsto.add inv_denominator_tendsto

theorem dimension_ratio_tendsto :
    Tendsto (fun n : ℕ ↦ (n : ℝ) / denominator n) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub
    (inv_denominator_tendsto.const_mul 2)
  have heq (n : ℕ) : (1 : ℝ) - 2 * (denominator n)⁻¹ =
      (n : ℝ) / denominator n := by
    unfold denominator
    field_simp
    ring
  simpa only [mul_zero, sub_zero] using h.congr (fun n ↦ heq n)

theorem cutoff_le_dimension_eventually : ∀ᶠ n in atTop, cutoff n ≤ n := by
  have hc := cutoff_ratio_tendsto.eventually_lt_const (show (0 : ℝ) < 1 / 2 by norm_num)
  have hn := dimension_ratio_tendsto.eventually_const_lt (show (1 : ℝ) / 2 < 1 by norm_num)
  filter_upwards [hc, hn] with n hc hn
  exact_mod_cast (le_of_lt ((div_lt_div_iff_of_pos_right (denominator_pos n)).mp
    (lt_trans hc hn)))

/-- Floor approximation before enforcing the permitted index range. -/
def floorIndex (x : ℝ) (n : ℕ) : ℕ := Nat.floor (x / Real.pi * denominator n)

theorem floor_ratio_tendsto (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun n ↦ (floorIndex x n : ℝ) / denominator n)
      atTop (𝓝 (x / Real.pi)) := by
  have hy : 0 ≤ x / Real.pi := div_nonneg hx Real.pi_pos.le
  have herr : Tendsto
      (fun n ↦ x / Real.pi - (floorIndex x n : ℝ) / denominator n) atTop (𝓝 0) := by
    apply squeeze_zero (g := fun n ↦ (denominator n)⁻¹)
    · intro n
      apply sub_nonneg.mpr
      exact (div_le_iff₀ (denominator_pos n)).mpr
        (Nat.floor_le (mul_nonneg hy (denominator_pos n).le))
    · intro n
      have hf := (Nat.lt_floor_add_one (x / Real.pi * denominator n)).le
      rw [← one_div]
      apply (le_div_iff₀ (denominator_pos n)).mpr
      have heq : (x / Real.pi - (floorIndex x n : ℝ) / denominator n) *
          denominator n = x / Real.pi * denominator n - (floorIndex x n : ℝ) := by
        rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt (denominator_pos n))]
      rw [heq]
      exact sub_le_iff_le_add.mpr (by simpa [floorIndex, add_comm] using hf)
    · exact inv_denominator_tendsto
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ x / Real.pi)
    atTop (𝓝 (x / Real.pi))).sub herr
  simpa only [sub_zero, sub_sub_cancel] using h

/-- Clipping enforces admissible source indices for all sufficiently large n.
The added `max 1` avoids any special convention for index zero. -/
def index (x : ℝ) (n : ℕ) : ℕ :=
  min n (max 1 (max (cutoff n) (floorIndex x n)))

theorem index_le_dimension (x : ℝ) (n : ℕ) : index x n ≤ n := min_le_left _ _

theorem index_admissible (x : ℝ) :
    ∀ᶠ n in atTop, 1 ≤ index x n ∧ cutoff n ≤ index x n ∧ index x n ≤ n := by
  filter_upwards [eventually_ge_atTop 1, cutoff_le_dimension_eventually] with n hn hc
  refine ⟨le_min hn (le_max_left _ _), le_min hc ?_, index_le_dimension x n⟩
  exact (le_max_left _ _).trans (le_max_right _ _)

theorem index_ratio_tendsto (x : ℝ) (hx : x ∈ Set.Icc 0 Real.pi) :
    Tendsto (fun n ↦ (index x n : ℝ) / denominator n) atTop (𝓝 (x / Real.pi)) := by
  have hnonneg : 0 ≤ x / Real.pi := div_nonneg hx.1 Real.pi_pos.le
  have hle : x / Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr hx.2
  have H := dimension_ratio_tendsto.min
    (inv_denominator_tendsto.max (cutoff_ratio_tendsto.max (floor_ratio_tendsto x hx.1)))
  simp only [max_eq_right hnonneg, min_eq_right hle] at H
  apply H.congr
  intro n
  simp only [index, Nat.cast_min, Nat.cast_max, Nat.cast_one]
  rw [← one_div, max_div_div_right (denominator_pos n).le,
    max_div_div_right (denominator_pos n).le,
    min_div_div_right (denominator_pos n).le]

def grid (n j : ℕ) : ℝ := (j : ℝ) * Real.pi / denominator n

def mesh (x : ℝ) (n : ℕ) : ℝ := grid n (index x n)

theorem mesh_tendsto (x : ℝ) (hx : x ∈ Set.Icc 0 Real.pi) :
    Tendsto (mesh x) atTop (𝓝 x) := by
  have H := (index_ratio_tendsto x hx).mul_const Real.pi
  rw [div_mul_cancel₀ x Real.pi_ne_zero] at H
  apply H.congr
  intro n
  dsimp [mesh, grid]
  ring

theorem mesh_mem (x : ℝ) (n : ℕ) : mesh x n ∈ Set.Icc 0 Real.pi := by
  have hj : (index x n : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (index_le_dimension x n)
  dsimp [mesh, grid]
  constructor
  · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) Real.pi_pos.le)
      (denominator_pos n).le
  · apply (div_le_iff₀ (denominator_pos n)).mpr
    have hdenom : (index x n : ℝ) ≤ denominator n := by
      unfold denominator
      linarith
    nlinarith [Real.pi_pos]

end MF21Mesh

#print axioms MF21Mesh.log_squared_ratio_tendsto
#print axioms MF21Mesh.cutoff_ratio_tendsto
#print axioms MF21Mesh.index_admissible
#print axioms MF21Mesh.mesh_tendsto
#print axioms MF21Mesh.mesh_mem
