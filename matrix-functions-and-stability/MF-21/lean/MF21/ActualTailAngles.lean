import MF21.ActualPhaseIndexing
import MF21.SymbolTransfer

open Set Filter
open scoped Topology
noncomputable section
namespace MF21Expansion
open MF21Challenge MF21Quantization MF21Phase MF21ActualBoundary

/-- The exact MF-21 Toeplitz eigenangles satisfy the exponentially accurate
implicit phase model with one fixed lower index, for every m>0. -/
theorem actual_tailAngleApproximation (m : ℕ) (hm : 0 < m) (model : Model m) :
    TailAngleApproximation m model := by
  obtain ⟨J,N,M,C,c,hJ,hN,hM,hC,hc,heta,hroots⟩ := actual_indexed_phase_roots m hm model
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp (step_tendsto.eventually_lt_const model.Hpos)
  refine ⟨J,max N N₁,2*C*Real.exp (c*(Real.pi/4+M)/3),c*Real.pi/3,
    Real.pi+Real.pi/4+M,by positivity,by positivity,by positivity,?_⟩
  intro n hn j hj
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := hN.trans hnN
  have ht := eigenangle_mem m n hm j
  have htc : eigenangle m n hm j ∈ Icc 0 Real.pi := ⟨le_of_lt ht.1,le_of_lt ht.2⟩
  have hh : step n ≤ model.H := (hN₁ n ((le_max_right _ _).trans hn)).le
  have hp : (grid n j,step n) ∈ Icc 0 Real.pi ×ˢ Icc 0 model.H :=
    ⟨grid_mem n j,(step_pos n).le,hh⟩
  obtain ⟨hcell,hres⟩ := hroots n hnN j hj
  have hcell' : |phase n model.eta (eigenangle m n hm j)-(j.val+1 : ℕ)*Real.pi| ≤ Real.pi/4 := by
    simpa only [Nat.cast_add,Nat.cast_one] using hcell
  have he := phase_cell_exp_bound model.eta M c hc n (j.val+1) hn1
    (eigenangle m n hm j) (le_of_lt ht.1) (heta _ htc) hcell'
  have hscale := phase_cell_angle_linear_bound model.eta M hM n (j.val+1) hn1
    (hJ.trans hj) (eigenangle m n hm j) (le_of_lt ht.1) (heta _ htc) hcell'
  refine ⟨eigenangle m n hm j,ht,(symbol_eigenangle m n hm j).symm,?_,?_⟩
  · have hd := model.inverse_distance (grid n j,step n) hp (eigenangle m n hm j) htc
    have hid : grid n j-(eigenangle m n hm j-step n*model.eta (eigenangle m n hm j)) =
        -(step n*(phase n model.eta (eigenangle m n hm j)-(j.val+1)*Real.pi)) := by
      rw [grid_eq]
      unfold phase step
      push_cast
      field_simp
      ring
    rw [hid,abs_neg,abs_mul,abs_of_nonneg (step_pos n).le,abs_sub_comm] at hd
    have hb := hres.trans (mul_le_mul_of_nonneg_left he (le_of_lt hC))
    calc
      |eigenangle m n hm j-model.Y (grid n j,step n)| ≤
          2*(step n*|phase n model.eta (eigenangle m n hm j)-(j.val+1)*Real.pi|) := hd
      _ ≤ 2*(step n*(C*(Real.exp (c*(Real.pi/4+M)/3)*
          Real.exp (-(c*Real.pi/3)*(j.val+1 : ℕ))))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (step_pos n).le) (by norm_num)
      _ = _ := by ring
  · simpa only [step,div_eq_mul_inv] using hscale

end MF21Expansion

#print axioms MF21Expansion.actual_tailAngleApproximation
