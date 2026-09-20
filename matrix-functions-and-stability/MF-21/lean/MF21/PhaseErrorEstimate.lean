import MF21.PhaseIndexing

open Set
open scoped Topology
noncomputable section
namespace MF21Phase

def phase (n : ℕ) (eta : ℝ → ℝ) (t : ℝ) : ℝ := ((n : ℝ)+2)*t-eta t

theorem phase_cell_angle_bounds (eta : ℝ → ℝ) (M : ℝ) (n j : ℕ)
    (hn : 1 ≤ n) (theta : ℝ) (htheta : 0 ≤ theta)
    (heta : |eta theta| ≤ M)
    (hcell : |phase n eta theta-j*Real.pi| ≤ Real.pi/4) :
    ((j : ℝ)*Real.pi-Real.pi/4-M)/3 ≤ (n : ℝ)*theta ∧
    theta ≤ ((j : ℝ)*Real.pi+Real.pi/4+M)/((n : ℝ)+2) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hη := abs_le.mp heta
  have hc := abs_le.mp hcell
  dsimp only [phase] at hc
  constructor
  · have hnon := mul_nonneg (show 0 ≤ (n : ℝ)-1 by linarith) htheta
    nlinarith
  · apply (le_div_iff₀ (by positivity : 0 < (n : ℝ)+2)).mpr
    nlinarith

theorem phase_cell_exp_bound (eta : ℝ → ℝ) (M c : ℝ) (hc : 0 < c)
    (n j : ℕ) (hn : 1 ≤ n) (theta : ℝ) (htheta : 0 ≤ theta)
    (heta : |eta theta| ≤ M)
    (hcell : |phase n eta theta-j*Real.pi| ≤ Real.pi/4) :
    Real.exp (-c*n*theta) ≤
      Real.exp (c*(Real.pi/4+M)/3) * Real.exp (-(c*Real.pi/3)*j) := by
  have hb := (phase_cell_angle_bounds eta M n j hn theta htheta heta hcell).1
  have hb' := mul_le_mul_of_nonneg_left hb (le_of_lt hc)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The exponential phase error, on the original mesh scale. -/
theorem phase_exponential_distance
    (eta deta E : ℝ → ℝ) (M C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (n j : ℕ) (hn : 1 ≤ n) (theta y : ℝ)
    (htheta : theta ∈ Icc 0 Real.pi) (hy : y ∈ Icc 0 Real.pi)
    (hd : ∀ t ∈ Icc 0 Real.pi, HasDerivAt (phase n eta) (deta t) t)
    (hdlower : ∀ t ∈ Icc 0 Real.pi, ((n : ℝ)+2)/2 ≤ deta t)
    (heta : |eta theta| ≤ M)
    (hcell : |phase n eta theta-j*Real.pi| ≤ Real.pi/4)
    (hz : Real.sin (phase n eta theta)+E theta = 0)
    (hyphase : phase n eta y = j*Real.pi)
    (hE : |E theta| ≤ C*Real.exp (-c*n*theta)) :
    |theta-y| ≤ (Real.pi*C*Real.exp (c*(Real.pi/4+M)/3)) *
      Real.exp (-(c*Real.pi/3)*j) / ((n : ℝ)+2) := by
  have hdistance := inverse_phase_displacement (phase n eta) deta 0 Real.pi
    (((n : ℝ)+2)/2) (by positivity) hd hdlower theta y htheta hy
  rw [hyphase] at hdistance
  have hres := phase_residual_bound (phase n eta theta) (E theta) j
    (hcell.trans (by linarith [Real.pi_pos])) hz
  have hexp := phase_cell_exp_bound eta M c hc n j hn theta htheta.1 heta hcell
  have herr := hE.trans (mul_le_mul_of_nonneg_left hexp hC)
  have hres' := hres.trans (mul_le_mul_of_nonneg_left herr (by positivity : 0 ≤ Real.pi/2))
  apply (le_div_iff₀ (by positivity : 0 < (n : ℝ)+2)).mpr
  nlinarith

theorem phase_cell_angle_linear_bound (eta : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (n j : ℕ) (hn : 1 ≤ n) (hj : 1 ≤ j) (theta : ℝ) (htheta : 0 ≤ theta)
    (heta : |eta theta| ≤ M)
    (hcell : |phase n eta theta-j*Real.pi| ≤ Real.pi/4) :
    theta ≤ (Real.pi+Real.pi/4+M)*j/((n : ℝ)+2) := by
  refine (phase_cell_angle_bounds eta M n j hn theta htheta heta hcell).2.trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  nlinarith [Real.pi_pos]

end MF21Phase

#print axioms MF21Phase.phase_exponential_distance
#print axioms MF21Phase.phase_cell_angle_linear_bound
