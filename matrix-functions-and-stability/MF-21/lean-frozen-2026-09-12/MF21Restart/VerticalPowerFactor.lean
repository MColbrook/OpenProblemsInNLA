import MF21Restart.ParametricTaylor

/-!
Repeated vertical differentiation of a power leaves the expected
undifferentiated power as a factor. The remaining factors are explicitly
defined and analytic. See `COEFFICIENT_VANISHING_STATEMENTS.md`.
-/

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace MF21Restart

def verticalPowerFactor (u : ℝ × ℝ → ℝ) (N : ℕ) : ℕ → ℝ × ℝ → ℝ
  | 0, _ => 1
  | k + 1, p =>
      ((N - k : ℕ) : ℝ) * verticalIteratedDeriv u 1 p * verticalPowerFactor u N k p +
        u p * verticalIteratedDeriv (verticalPowerFactor u N k) 1 p

/-- Every explicitly defined residual factor is analytic wherever u is. -/
theorem verticalPowerFactor_contDiffAt
    (u : ℝ × ℝ → ℝ) (N k : ℕ) (p : ℝ × ℝ) (hu : ContDiffAt ℝ ⊤ u p) :
    ContDiffAt ℝ ⊤ (verticalPowerFactor u N k) p := by
  induction k with
  | zero => exact contDiffAt_const
  | succ k ih =>
    exact ((contDiffAt_const.mul (verticalIteratedDeriv_contDiffAt u p hu 1)).mul ih).add
      (hu.mul (verticalIteratedDeriv_contDiffAt (verticalPowerFactor u N k) p ih 1))

set_option backward.isDefEq.respectTransparency.types false in
/-- The exact factorization follows from differentiating the preceding
identity on a neighborhood, using the ordinary power and product rules. -/
theorem verticalIteratedDeriv_pow_factor
    (u : ℝ × ℝ → ℝ) (N k : ℕ) (p : ℝ × ℝ)
    (hu : ContDiffAt ℝ ⊤ u p) (hk : k ≤ N) :
    verticalIteratedDeriv (fun q => u q ^ N) k p =
      u p ^ (N - k) * verticalPowerFactor u N k p := by
  induction k generalizing p with
  | zero => simp [verticalIteratedDeriv, verticalPowerFactor]
  | succ k ih =>
    have hkN : k ≤ N := by omega
    have htendsto : Filter.Tendsto (fun t : ℝ => (p.1, t)) (𝓝 p.2) (𝓝 p) :=
      (continuous_const.prodMk continuous_id).continuousAt.tendsto
    have hnear : ∀ᶠ t in 𝓝 p.2, ContDiffAt ℝ ⊤ u (p.1, t) :=
      htendsto.eventually (hu.eventually (by simp))
    have heq : (fun t : ℝ => verticalIteratedDeriv (fun q => u q ^ N) k (p.1, t))
        =ᶠ[𝓝 p.2]
        (fun t : ℝ => u (p.1, t) ^ (N - k) * verticalPowerFactor u N k (p.1, t)) := by
      filter_upwards [hnear] with t ht
      exact ih (p.1, t) ht hkN
    have huc : ContDiffAt ℝ ⊤ (fun t : ℝ => u (p.1, t)) p.2 :=
      hu.comp p.2 (contDiffAt_const.prodMk contDiffAt_id)
    have hAc : ContDiffAt ℝ ⊤ (fun t : ℝ => verticalPowerFactor u N k (p.1, t)) p.2 :=
      (verticalPowerFactor_contDiffAt u N k p hu).comp p.2
        (contDiffAt_const.prodMk contDiffAt_id)
    have huD : HasDerivAt (fun t : ℝ => u (p.1, t)) (verticalIteratedDeriv u 1 p) p.2 := by
      simpa only [verticalIteratedDeriv, iteratedDeriv_one] using
        (huc.differentiableAt (by simp)).hasDerivAt
    have hAD : HasDerivAt (fun t : ℝ => verticalPowerFactor u N k (p.1, t))
        (verticalIteratedDeriv (verticalPowerFactor u N k) 1 p) p.2 := by
      simpa only [verticalIteratedDeriv, iteratedDeriv_one] using
        (hAc.differentiableAt (by simp)).hasDerivAt
    have hd := ((huD.pow (N - k)).mul hAD).deriv
    have hsub : N - k - 1 = N - (k + 1) := by omega
    have hsucc : N - k = N - (k + 1) + 1 := by omega
    calc
      verticalIteratedDeriv (fun q => u q ^ N) (k + 1) p =
          deriv (fun t : ℝ =>
            u (p.1, t) ^ (N - k) * verticalPowerFactor u N k (p.1, t)) p.2 := by
        simpa only [verticalIteratedDeriv, iteratedDeriv_succ] using heq.deriv_eq
      _ = (((N - k : ℕ) : ℝ) * u p ^ (N - k - 1) * verticalIteratedDeriv u 1 p) *
            verticalPowerFactor u N k p +
          u p ^ (N - k) * verticalIteratedDeriv (verticalPowerFactor u N k) 1 p := hd
      _ = u p ^ (N - (k + 1)) * verticalPowerFactor u N (k + 1) p := by
        simp only [verticalPowerFactor]
        rw [hsub, hsucc, pow_succ]
        ring

#print axioms verticalPowerFactor_contDiffAt
#print axioms verticalIteratedDeriv_pow_factor

end MF21Restart
