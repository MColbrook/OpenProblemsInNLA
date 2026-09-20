import MF21.FiniteTraceObstruction
import MF21.ToeplitzTraceLimit
import MF21.SpectralBounds
import MF21.QuantizationTaylor
import MF21.LogSquaredMesh

/-! The unconditional fixed-finite-index obstruction for the actual spectrum. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Topology
open Filter Finset Set
namespace MF21Obstruction

/-- Zero-based extension, used only to state finite-head limits with fixed indices. -/
def paddedEigenvalue (m n j : ℕ) : ℝ :=
  if hj : j < n then MF21Challenge.eigenvalue m n ⟨j,hj⟩ else 0

def scaledEigenvalue (m n j : ℕ) : ℝ :=
  ((n : ℝ)+2)^(2*m) * paddedEigenvalue m n j

def profile (m j : ℕ) : ℝ :=
  (((j : ℝ)+1)*Real.pi + ((m : ℝ)-1)*Real.pi/2)^(2*m)

theorem profile_pos (m : ℕ) (hm : 3 ≤ m) (j : ℕ) : 0 < profile m j := by
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  unfold profile
  apply pow_pos
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  nlinarith [Real.pi_pos]

theorem profile_inverse (m j : ℕ) :
    (profile m j)⁻¹ = (Real.pi^(2*m))⁻¹ *
      (1/((j : ℝ)+1+((m : ℝ)-1)/2)^(2*m)) := by
  unfold profile
  rw [show ((j : ℝ)+1)*Real.pi+((m : ℝ)-1)*Real.pi/2 =
    Real.pi*((j : ℝ)+1+((m : ℝ)-1)/2) by ring, mul_pow, mul_inv_rev]
  ring

theorem profile_inverse_summable (m : ℕ) (hm : 3 ≤ m) :
    Summable (fun j => (profile m j)⁻¹) := by
  simp_rw [profile_inverse]
  exact (MF21Audit.modelTrace_series_summable m hm).mul_left _

theorem profile_inverse_sum (m : ℕ) :
    (∑' j, (profile m j)⁻¹) = MF21Audit.modelTrace m := by
  simp_rw [profile_inverse]
  exact tsum_mul_left

theorem scaled_inverse_sum (m n : ℕ) :
    (∑ j ∈ range n, (scaledEigenvalue m n j)⁻¹) =
      (∑ j : Fin n, (MF21Challenge.eigenvalue m n j)⁻¹) / ((n : ℝ)+2)^(2*m) := by
  rw [← Fin.sum_univ_eq_sum_range (fun j => (scaledEigenvalue m n j)⁻¹) n]
  simp only [scaledEigenvalue, paddedEigenvalue, dif_pos (Fin.isLt _), mul_inv_rev]
  rw [← sum_mul]
  rfl

/-- A fixed finite set of actual eigenvalues differs from the shifted model,
for every sufficiently large dimension, by a fixed positive scaled amount. -/
theorem actual_finite_head_separation (m : ℕ) (hm : 3 ≤ m) :
    ∃ J : ℕ, 0 < J ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ n in atTop, J ≤ n ∧ ∃ j < J, ε < |scaledEigenvalue m n j-profile m j| := by
  apply MF21Audit.finite_head_separation_of_finite_inverse_trace
    (scaledEigenvalue m) (profile m)
    (fun j => (m : ℝ)^(2*m)/((j : ℝ)+1)^(2*m))
    (MF21Audit.kernelTraceConstant m : ℝ)
  · intro n j hj
    simp only [scaledEigenvalue, paddedEigenvalue, dif_pos hj]
    exact mul_pos (by positivity) (MF21Challenge.eigenvalue_pos m n ⟨j,hj⟩)
  · exact profile_pos m hm
  · exact profile_inverse_summable m hm
  · exact MF21Circulant.reciprocal_majorant_summable m (by omega)
  · intro j hj
    positivity
  · intro n j hj hjn
    simpa only [scaledEigenvalue, paddedEigenvalue, dif_pos hjn] using
      MF21Circulant.scaled_reciprocal_majorant m n (by omega) ⟨j,hjn⟩ hj
  · simpa only [scaled_inverse_sum] using MF21TraceLimit.eigenvalue_inverse_sum_tendsto m (by omega)
  · rw [profile_inverse_sum]
    exact MF21Audit.kernelTraceConstant_ne_modelTrace m hm


def spacing (n : ℕ) : ℝ := ((n : ℝ)+2)⁻¹

theorem spacing_pos (n : ℕ) : 0 < spacing n := by unfold spacing; positivity

theorem spacing_tendsto : Tendsto spacing atTop (𝓝 0) :=
  MF21Mesh.inv_denominator_tendsto

def approximation {m : ℕ} (model : MF21Quantization.Model m) (n j : ℕ) : ℝ :=
  ∑ k ∈ range (2*m+1), model.d k (((j : ℝ)+1)*Real.pi*spacing n)*spacing n^k

theorem approximation_profile {m : ℕ} (model : MF21Quantization.Model m) (j : ℕ) :
    Tendsto (fun n => approximation model n j / spacing n^(2*m)) atTop (𝓝 (profile m j)) := by
  let c : ℝ := ((j : ℝ)+1)*Real.pi
  have hc : 0 < c := by dsimp [c]; positivity
  have hmem : ∀ᶠ n in atTop,
      c*spacing n ∈ Icc 0 Real.pi ∧ spacing n ∈ Ioc 0 model.H := by
    have hs0 : Tendsto (fun n => c*spacing n) atTop (𝓝 0) := by
      simpa only [mul_zero] using spacing_tendsto.const_mul c
    have hs := hs0.eventually_lt_const Real.pi_pos
    have hh := spacing_tendsto.eventually_lt_const model.Hpos
    filter_upwards [hs,hh] with n hn hH
    exact ⟨⟨mul_nonneg hc.le (spacing_pos n).le, by simpa only [mul_zero] using hn.le⟩, spacing_pos n,hH.le⟩
  exact model.coefficient_fixed_index_profile c spacing spacing_tendsto hmem

/-- The order-2m Taylor family has an eventual lower bound on a fixed finite
head, on the original h^(2m) scale. -/
theorem model_finite_head_lower_bound (m : ℕ) (hm : 3 ≤ m)
    (model : MF21Quantization.Model m) :
    ∃ J : ℕ, 0 < J ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ n in atTop, J ≤ n ∧ ∃ j < J,
        ε*spacing n^(2*m) < |paddedEigenvalue m n j-approximation model n j| := by
  obtain ⟨J,hJ,ε,hε,hsep⟩ := actual_finite_head_separation m hm
  have hsep' : ∀ᶠ n in atTop, ∃ j < J,
      ε < |paddedEigenvalue m n j/spacing n^(2*m)-profile m j| := by
    filter_upwards [hsep] with n hn
    obtain ⟨j,hj,hje⟩ := hn.2
    refine ⟨j,hj,?_⟩
    simpa only [scaledEigenvalue, spacing, inv_pow, div_inv_eq_mul, mul_comm] using hje
  have hlower := MF21Audit.finite_head_scaled_remainder_lower_bound
    (paddedEigenvalue m) (approximation model) spacing (profile m) (2*m) J ε
    spacing_pos hε hsep' (fun j _ => approximation_profile model j)
  refine ⟨J,hJ,ε/2,by positivity,?_⟩
  filter_upwards [hlower,eventually_ge_atTop J] with n hn hnJ
  exact ⟨hnJ,hn⟩


theorem remainder_eq {m : ℕ} (model : MF21Quantization.Model m) (n : ℕ) (j : Fin n) :
    MF21Challenge.remainder m (2*m) n model.d j =
      paddedEigenvalue m n j.val-approximation model n j.val := by
  unfold MF21Challenge.remainder paddedEigenvalue approximation
  simp only [dif_pos j.isLt]
  congr 1
  apply sum_congr rfl
  intro k _
  have hg : MF21Challenge.grid n j = ((j.val : ℝ)+1)*Real.pi*spacing n := by
    simp [MF21Challenge.grid, spacing, div_eq_mul_inv]
  rw [hg, spacing, inv_pow, div_eq_mul_inv]

/-- Sharpness on the source grid: every sufficiently large dimension has an
error of order at least h^(2m) within one fixed finite set of indices. -/
theorem model_finite_head_remainder (m : ℕ) (hm : 3 ≤ m)
    (model : MF21Quantization.Model m) :
    ∃ J : ℕ, 0 < J ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ n in atTop, ∃ j : Fin n, j.val < J ∧
        ε/((n : ℝ)+2)^(2*m) < |MF21Challenge.remainder m (2*m) n model.d j| := by
  obtain ⟨J,hJ,ε,hε,hsep⟩ := model_finite_head_lower_bound m hm model
  refine ⟨J,hJ,ε,hε,?_⟩
  filter_upwards [hsep] with n hn
  obtain ⟨j,hj,hje⟩ := hn.2
  let jn : Fin n := ⟨j,hj.trans_le hn.1⟩
  refine ⟨jn,hj,?_⟩
  rw [remainder_eq]
  simpa only [spacing, inv_pow, div_eq_mul_inv] using hje

/-- The chosen common smooth family cannot satisfy the next uniform order.
This is a theorem about the actual Toeplitz eigenvalues, with no analytic
asymptotic hypothesis remaining. -/
theorem model_not_uniform (m : ℕ) (hm : 3 ≤ m)
    (model : MF21Quantization.Model m) : ¬MF21Challenge.UniformOrder m (2*m) model.d := by
  obtain ⟨J,hJ,ε,hε,hsep⟩ := model_finite_head_remainder m hm model
  intro ⟨D,hD,N,huniform⟩
  have hlarge : ∀ᶠ n : ℕ in atTop, D/ε < (n : ℝ)+2 :=
    MF21Mesh.denominator_atTop.eventually_gt_atTop (D/ε)
  obtain ⟨n,hnsep,hnN,hnlarge⟩ := (hsep.and ((eventually_ge_atTop N).and hlarge)).exists
  obtain ⟨j,hj,hje⟩ := hnsep
  have hu := huniform n hnN j
  have hd : 0 < (n : ℝ)+2 := by positivity
  have hp : 0 < ((n : ℝ)+2)^(2*m) := pow_pos hd _
  have hstrict := hje.trans_le hu
  have hsmall : ε*((n : ℝ)+2) < D := by
    rw [pow_succ] at hstrict
    have he := (div_lt_div_iff₀ hp (mul_pos hp hd)).mp hstrict
    nlinarith
  have hbig : D < ε*((n : ℝ)+2) := by
    have h := (div_lt_iff₀ hε).mp hnlarge
    nlinarith
  linarith

end MF21Obstruction
#print axioms MF21Obstruction.actual_finite_head_separation

#print axioms MF21Obstruction.model_finite_head_lower_bound

#print axioms MF21Obstruction.model_not_uniform
#print axioms MF21Obstruction.model_finite_head_remainder
