import MF21Restart.FourierStencil
import MF21Restart.EigenvalueBridge
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
The strict spectral enclosure used before manuscript Lemma 4. The proof
uses the actual Fourier integral quadratic form. Fourier orthogonality at
m=0 makes the unweighted squared trigonometric polynomial have positive
integral for every nonzero vector. Both desired weights are positive away
from finitely many points, which proves strict weighted positivity.

The statement lock is `SPECTRAL_ENCLOSURE_STATEMENTS.md`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory Filter Matrix

namespace MF21Restart

private def spectralTrigNormSq (n : ℕ) (v : Fin n → ℝ) (θ : ℝ) : ℝ :=
  (∑ i : Fin n, v i * Real.cos ((i.val : ℝ) * θ)) ^ 2 +
    (∑ i : Fin n, v i * Real.sin ((i.val : ℝ) * θ)) ^ 2

private theorem spectralTrigNormSq_nonneg (n : ℕ) (v : Fin n → ℝ) (θ : ℝ) :
    0 ≤ spectralTrigNormSq n v θ :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

private theorem spectralTrigNormSq_continuous (n : ℕ) (v : Fin n → ℝ) :
    Continuous (spectralTrigNormSq n v) := by
  unfold spectralTrigNormSq
  fun_prop

private theorem spectralTrigNormSq_eq_sum (n : ℕ) (v : Fin n → ℝ) (θ : ℝ) :
    spectralTrigNormSq n v θ =
      ∑ i : Fin n, ∑ j : Fin n,
        v i * v j * Real.cos ((((i.val : ℤ) - j.val : ℤ) : ℝ) * θ) := by
  unfold spectralTrigNormSq
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  rw [sub_mul, Real.cos_sub]
  ring

private theorem spectral_fourier_quadratic_integral
    (m n : ℕ) (v : Fin n → ℝ) :
    star v ⬝ᵥ ((toeplitz m n) *ᵥ v) =
      (1 / (2 * Real.pi)) *
        ∫ θ in -Real.pi..Real.pi, symbol m θ * spectralTrigNormSq n v θ := by
  let f : Fin n → Fin n → ℝ → ℝ := fun i j θ =>
    v i * (symbol m θ *
      Real.cos ((((i.val : ℤ) - j.val : ℤ) : ℝ) * θ)) * v j
  have hf (i j : Fin n) : Continuous (f i j) := by
    dsimp [f]
    unfold symbol
    fun_prop
  have hrow (i : Fin n) : Continuous (fun θ => ∑ j : Fin n, f i j θ) :=
    continuous_finsetSum _ (fun j _ => hf i j)
  have hfun (θ : ℝ) : (∑ i : Fin n, ∑ j : Fin n, f i j θ) =
      symbol m θ * spectralTrigNormSq n v θ := by
    rw [spectralTrigNormSq_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [f]
    ring
  calc
    star v ⬝ᵥ ((toeplitz m n) *ᵥ v) =
        ∑ i : Fin n, ∑ j : Fin n,
          v i * fourierCoeff m ((i.val : ℤ) - j.val) * v j := by
      simp only [dotProduct, Matrix.mulVec, toeplitz, Pi.star_apply, star_trivial,
        Finset.mul_sum, mul_assoc]
    _ = (1 / (2 * Real.pi)) *
        ∑ i : Fin n, ∑ j : Fin n, ∫ θ in -Real.pi..Real.pi, f i j θ := by
      simp only [f, fourierCoeff, intervalIntegral.integral_mul_const,
        intervalIntegral.integral_const_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (1 / (2 * Real.pi)) *
        ∫ θ in -Real.pi..Real.pi, ∑ i : Fin n, ∑ j : Fin n, f i j θ := by
      rw [intervalIntegral.integral_finsetSum
        (fun i _ => (hrow i).intervalIntegrable (-Real.pi) Real.pi)]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact (intervalIntegral.integral_finsetSum
        (fun j _ => (hf i j).intervalIntegrable (-Real.pi) Real.pi)).symm
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro θ _
      exact hfun θ

private theorem spectral_toeplitz_zero (n : ℕ) :
    toeplitz 0 n = (1 : Matrix (Fin n) (Fin n) ℝ) := by
  classical
  ext i j
  simp [toeplitz, fourierCoeff_zero, Matrix.one_apply, sub_eq_zero, Fin.ext_iff]

private theorem spectral_unweighted_integral (n : ℕ) (v : Fin n → ℝ) :
    star v ⬝ᵥ v =
      (1 / (2 * Real.pi)) * ∫ θ in -Real.pi..Real.pi, spectralTrigNormSq n v θ := by
  simpa only [spectral_toeplitz_zero, Matrix.one_mulVec, symbol, Nat.mul_zero,
    pow_zero, one_mul] using spectral_fourier_quadratic_integral 0 n v

private theorem spectral_unweighted_integral_pos
    (n : ℕ) (v : Fin n → ℝ) (hv : v ≠ 0) :
    0 < ∫ θ in -Real.pi..Real.pi, spectralTrigNormSq n v θ := by
  have hpos : 0 < star v ⬝ᵥ v := dotProduct_star_self_pos_iff.mpr hv
  rw [spectral_unweighted_integral] at hpos
  exact (mul_pos_iff_of_pos_left (by positivity : 0 < (1 : ℝ) / (2 * Real.pi))).mp hpos

/-- Strict positivity is preserved by a continuous weight positive off the
finite exceptional points 0 and the interval endpoints. The nonzero
unweighted integral, rather than an assumed polynomial root theorem,
prevents the integrand from vanishing almost everywhere. -/
private theorem spectral_weighted_integral_pos
    (w p : ℝ → ℝ) (hw : Continuous w) (hp : Continuous p)
    (hpnonneg : ∀ θ, 0 ≤ p θ)
    (hpint : 0 < ∫ θ in -Real.pi..Real.pi, p θ)
    (hwpos : ∀ θ ∈ Set.Ioo (-Real.pi) Real.pi, θ ≠ 0 → 0 < w θ) :
    0 < ∫ θ in -Real.pi..Real.pi, w θ * p θ := by
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hwAE : ∀ᵐ θ ∂volume.restrict (Set.Ioc (-Real.pi) Real.pi), 0 < w θ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (volume.ae_ne (0 : ℝ)),
      ae_restrict_of_ae (volume.ae_ne Real.pi)] with θ hθ hθ0 hθpi
    exact hwpos θ ⟨hθ.1, lt_of_le_of_ne hθ.2 hθpi⟩ hθ0
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (-Real.pi) Real.pi)]
      (fun θ => w θ * p θ) :=
    hwAE.mono (fun θ hθ => mul_nonneg hθ.le (hpnonneg θ))
  have hintnonneg : 0 ≤ ∫ θ in -Real.pi..Real.pi, w θ * p θ := by
    rw [intervalIntegral.integral_of_le hab]
    exact MeasureTheory.integral_nonneg_of_ae hnonneg
  by_contra hnot
  have hzero : (∫ θ in -Real.pi..Real.pi, w θ * p θ) = 0 :=
    le_antisymm (le_of_not_gt hnot) hintnonneg
  have hzeroAE :=
    (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hab hnonneg
      ((hw.mul hp).intervalIntegrable (-Real.pi) Real.pi)).mp hzero
  have hpzero : p =ᵐ[volume.restrict (Set.Ioc (-Real.pi) Real.pi)] 0 := by
    filter_upwards [hwAE, hzeroAE] with θ hwθ hzeroθ
    change w θ * p θ = 0 at hzeroθ
    exact (mul_eq_zero.mp hzeroθ).resolve_left (ne_of_gt hwθ)
  have hpnonnegAE : 0 ≤ᵐ[volume.restrict (Set.Ioc (-Real.pi) Real.pi)] p :=
    Filter.Eventually.of_forall hpnonneg
  have hpintzero : (∫ θ in -Real.pi..Real.pi, p θ) = 0 :=
    (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hab hpnonnegAE
      (hp.intervalIntegrable (-Real.pi) Real.pi)).mpr hpzero
  linarith

private theorem spectral_symbol_pos (m : ℕ) (θ : ℝ)
    (hθ : θ ∈ Set.Ioo (-Real.pi) Real.pi) (hθ0 : θ ≠ 0) :
    0 < symbol m θ := by
  have hs : Real.sin (θ / 2) ≠ 0 := by
    intro hzero
    have hhalf := (Real.sin_eq_zero_iff_of_lt_of_lt
      (by linarith [Real.pi_pos, hθ.1] : -Real.pi < θ / 2)
      (by linarith [Real.pi_pos, hθ.2] : θ / 2 < Real.pi)).mp hzero
    exact hθ0 (by linarith)
  have hbase : 0 < (2 * Real.sin (θ / 2)) ^ 2 :=
    sq_pos_of_ne_zero (mul_ne_zero (by norm_num) hs)
  simpa only [symbol, ← pow_mul] using pow_pos hbase m

private theorem spectral_symbol_lt_four_pow (m : ℕ) (hm : 1 ≤ m) (θ : ℝ)
    (hθ : θ ∈ Set.Ioo (-Real.pi) Real.pi) : symbol m θ < (4 : ℝ) ^ m := by
  have hc : 0 < Real.cos (θ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hbase : (2 * Real.sin (θ / 2)) ^ 2 < (4 : ℝ) := by
    nlinarith [Real.sin_sq_add_cos_sq (θ / 2), sq_pos_of_pos hc]
  have hpow := pow_lt_pow_left₀ hbase (sq_nonneg (2 * Real.sin (θ / 2)))
    (by omega : m ≠ 0)
  simpa only [symbol, ← pow_mul] using hpow

theorem toeplitz_posDef (m n : ℕ) (hm : 1 ≤ m) : (toeplitz m n).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (toeplitz_isHermitian m n)
  intro v hv
  rw [spectral_fourier_quadratic_integral]
  apply mul_pos (by positivity : 0 < (1 : ℝ) / (2 * Real.pi))
  exact spectral_weighted_integral_pos (symbol m) (spectralTrigNormSq n v)
    (by unfold symbol; fun_prop) (spectralTrigNormSq_continuous n v)
    (spectralTrigNormSq_nonneg n v) (spectral_unweighted_integral_pos n v hv)
    (spectral_symbol_pos m)

private theorem spectral_upper_quadratic_integral
    (m n : ℕ) (v : Fin n → ℝ) :
    star v ⬝ᵥ ((((4 : ℝ) ^ m) • (1 : Matrix (Fin n) (Fin n) ℝ) -
        toeplitz m n) *ᵥ v) =
      (1 / (2 * Real.pi)) * ∫ θ in -Real.pi..Real.pi,
        ((4 : ℝ) ^ m - symbol m θ) * spectralTrigNormSq n v θ := by
  have hp := spectralTrigNormSq_continuous n v
  have hgp : Continuous (fun θ => symbol m θ * spectralTrigNormSq n v θ) :=
    (show Continuous (symbol m) by unfold symbol; fun_prop).mul hp
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul, spectral_unweighted_integral,
    spectral_fourier_quadratic_integral]
  have hfun : (fun θ => ((4 : ℝ) ^ m - symbol m θ) * spectralTrigNormSq n v θ) =
      (fun θ => (4 : ℝ) ^ m * spectralTrigNormSq n v θ -
        symbol m θ * spectralTrigNormSq n v θ) := by
    funext θ
    ring
  have hconst : IntervalIntegrable
      (fun θ => (4 : ℝ) ^ m * spectralTrigNormSq n v θ) volume (-Real.pi) Real.pi :=
    (continuous_const.mul hp).intervalIntegrable _ _
  rw [hfun, intervalIntegral.integral_sub hconst
    (hgp.intervalIntegrable (-Real.pi) Real.pi),
    intervalIntegral.integral_const_mul]
  ring

theorem toeplitz_upper_complement_posDef (m n : ℕ) (hm : 1 ≤ m) :
    (((4 : ℝ) ^ m) • (1 : Matrix (Fin n) (Fin n) ℝ) - toeplitz m n).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    ((Matrix.isHermitian_one.smul
      (by simp only [isSelfAdjoint_iff, star_trivial] : IsSelfAdjoint ((4 : ℝ) ^ m))).sub
      (toeplitz_isHermitian m n))
  intro v hv
  rw [spectral_upper_quadratic_integral]
  apply mul_pos (by positivity : 0 < (1 : ℝ) / (2 * Real.pi))
  apply spectral_weighted_integral_pos (fun θ => (4 : ℝ) ^ m - symbol m θ)
    (spectralTrigNormSq n v)
    (by unfold symbol; fun_prop) (spectralTrigNormSq_continuous n v)
    (spectralTrigNormSq_nonneg n v) (spectral_unweighted_integral_pos n v hv)
  intro θ hθ _
  exact sub_pos.mpr (spectral_symbol_lt_four_pow m hm θ hθ)

/-- Both strict inequalities concern the actual published one-based range. -/
theorem eigenvalue_strict_spectral_enclosure
    (m n j : ℕ) (hm : 1 ≤ m) (hj : 1 ≤ j) (hjn : j ≤ n) :
    0 < eigenvalue m n j ∧ eigenvalue m n j < (4 : ℝ) ^ m := by
  let lam : ℝ := eigenvalue m n j
  have hroot : (toeplitz m n).charpoly.IsRoot lam :=
    (eigenvalue_index_iff_charpoly_root m n lam).mp ⟨j, hj, hjn, rfl⟩
  have hEig : Module.End.HasEigenvalue (toeplitz m n).mulVecLin lam := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_mulVecLin]
    exact hroot
  obtain ⟨v, hv⟩ := hEig.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hAv : (toeplitz m n) *ᵥ v = lam • v := by
    simpa only [Matrix.mulVecLin_apply] using hv.apply_eq_smul
  have hvpos : 0 < star v ⬝ᵥ v := dotProduct_star_self_pos_iff.mpr hv0
  have hlow := (toeplitz_posDef m n hm).dotProduct_mulVec_pos hv0
  rw [hAv, dotProduct_smul, smul_eq_mul] at hlow
  have hupp := (toeplitz_upper_complement_posDef m n hm).dotProduct_mulVec_pos hv0
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hAv, dotProduct_sub,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hupp
  have hupp' : 0 < ((4 : ℝ) ^ m - lam) * (star v ⬝ᵥ v) := by nlinarith
  exact ⟨(mul_pos_iff_of_pos_right hvpos).mp hlow,
    sub_pos.mp ((mul_pos_iff_of_pos_right hvpos).mp hupp')⟩

#print axioms toeplitz_posDef
#print axioms toeplitz_upper_complement_posDef
#print axioms eigenvalue_strict_spectral_enclosure

end MF21Restart
