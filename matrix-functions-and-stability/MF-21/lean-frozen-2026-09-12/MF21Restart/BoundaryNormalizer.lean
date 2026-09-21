import MF21Restart.RootListProducts
import MF21Restart.BoundaryConjugation
import MF21Restart.PhaseProduct

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MF21Restart

theorem stableRootList_injective (m : ℕ) (θ : ℝ) (hθ : 0 < θ) (hθπ : θ ≤ Real.pi) :
    Function.Injective (stableRootList m θ) := by
  intro a b hab
  have ha := a.isLt
  have hb := b.isLt
  have hidx : (⟨a.val + 1, ⟨by omega, by omega⟩⟩ : {ell : ℕ // 1 ≤ ell ∧ ell < m}) =
      ⟨b.val + 1, ⟨by omega, by omega⟩⟩ :=
    stableRootCurve_rootKappa_injective m θ hθ hθπ hab
  have hv := congrArg Subtype.val hidx
  change a.val + 1 = b.val + 1 at hv
  exact Fin.ext (by omega)

theorem exteriorRootList_injective (m : ℕ) (θ : ℝ) (hθ : 0 < θ) (hθπ : θ ≤ Real.pi) :
    Function.Injective (exteriorRootList m θ) := by
  intro a b hab
  apply stableRootList_injective m θ hθ hθπ
  exact inv_inj.mp hab

theorem stableRootList_contDiff (m : ℕ) (ell : Fin (m - 1)) :
    ContDiff ℝ ⊤ (fun θ : ℝ => stableRootList m θ ell) :=
  stableRootCurve_contDiff _ (rootKappa_re_pos m (ell.val + 1)
    (by omega) (by have := ell.isLt; omega))

theorem exteriorRootList_contDiff (m : ℕ) (ell : Fin (m - 1)) :
    ContDiff ℝ ⊤ (fun θ : ℝ => exteriorRootList m θ ell) := by
  convert! (stableRootList_contDiff m ell).inv
    (fun θ => stableRootCurve_ne_zero (rootKappa m (ell.val + 1)) θ) using 1

theorem manuscriptPhaseProduct_contDiff (m : ℕ) (hm : 1 ≤ m) :
    ContDiff ℝ ⊤ (manuscriptPhaseProduct m) := by
  have hr : ContDiff ℝ ⊤ (fun θ : ℝ => 2 * Real.sin (θ / 2)) := by fun_prop
  have hc : ContDiff ℝ ⊤ (fun θ : ℝ => ((2 * Real.sin (θ / 2) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hr
  have heq : manuscriptPhaseProduct m = fun θ =>
      ((2 * Real.sin (θ / 2) : ℝ) : ℂ) ^ (m - 1) * normalizedPhaseProduct m θ := by
    funext θ
    exact manuscriptPhaseProduct_factorization m θ
  rw [heq]
  exact (hc.pow _).mul (normalizedPhaseProduct_contDiff m hm)

private theorem contDiff_vandermonde_of_entries (k : ℕ) (v : ℝ → Fin k → ℂ)
    (hv : ∀ i, ContDiff ℝ ⊤ (fun θ : ℝ => v θ i)) :
    ContDiff ℝ ⊤ (fun θ : ℝ => (Matrix.vandermonde (v θ)).det) := by
  have heq : (fun θ : ℝ => (Matrix.vandermonde (v θ)).det) = fun θ =>
      ∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (v θ j - v θ i) := by
    funext θ
    exact Matrix.det_vandermonde _
  rw [heq]
  exact contDiff_prod (fun i _ => contDiff_prod (fun j _ => (hv j).sub (hv i)))

def manuscriptNormalizer (m n : ℕ) (θ : ℝ) : ℂ :=
  (-2 * Complex.I) *
    ((Matrix.vandermonde (stableRootList m θ)).det *
      (Matrix.vandermonde (exteriorRootList m θ)).det) *
    boundaryExteriorProduct m θ ^ (n + m + 1) *
    (Complex.normSq (manuscriptPhaseProduct m θ) : ℂ)

theorem manuscriptNormalizer_contDiff (m n : ℕ) (hm : 2 ≤ m) :
    ContDiff ℝ ⊤ (manuscriptNormalizer m n) := by
  have hm1 : 1 ≤ m := by omega
  have hf := manuscriptPhaseProduct_contDiff m hm1
  have hr : ContDiff ℝ ⊤ (fun θ : ℝ => (manuscriptPhaseProduct m θ).re) :=
    Complex.reCLM.contDiff.comp hf
  have hi : ContDiff ℝ ⊤ (fun θ : ℝ => (manuscriptPhaseProduct m θ).im) :=
    Complex.imCLM.contDiff.comp hf
  have hsq : ContDiff ℝ ⊤ (fun θ : ℝ => (Complex.normSq (manuscriptPhaseProduct m θ) : ℂ)) := by
    simpa only [Complex.normSq_apply, Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.comp ((hr.mul hr).add (hi.mul hi))
  exact ((contDiff_const.mul
    ((contDiff_vandermonde_of_entries _ _ (stableRootList_contDiff m)).mul
      (contDiff_vandermonde_of_entries _ _ (exteriorRootList_contDiff m)))).mul
      ((boundaryExteriorProduct_contDiff m hm).pow _)).mul hsq

theorem manuscriptNormalizer_ne_zero (m n : ℕ) (hm : 2 ≤ m)
    (θ : ℝ) (hθ : 0 < θ) (hθπ : θ ≤ Real.pi) :
    manuscriptNormalizer m n θ ≠ 0 := by
  have hR : (Matrix.vandermonde (stableRootList m θ)).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr (stableRootList_injective m θ hθ hθπ)
  have hO : (Matrix.vandermonde (exteriorRootList m θ)).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr (exteriorRootList_injective m θ hθ hθπ)
  have hphase : (Complex.normSq (manuscriptPhaseProduct m θ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Complex.normSq_pos.mpr
      (manuscriptPhaseProduct_ne_zero m (by omega) θ hθ hθπ)))
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (by norm_num) Complex.I_ne_zero) (mul_ne_zero hR hO))
      (pow_ne_zero _ (boundaryExteriorProduct_ne_zero m θ))) hphase

theorem manuscriptNormalizer_conj (m n : ℕ) (hm : 2 ≤ m) (θ : ℝ) :
    (starRingEnd ℂ) (manuscriptNormalizer m n θ) = -manuscriptNormalizer m n θ := by
  unfold manuscriptNormalizer
  rw [map_mul, map_mul, map_mul, rootVandermondeProduct_conj, map_pow,
    boundaryExteriorProduct_conj m (by omega)]
  simp only [map_mul, map_neg, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  ring

def manuscriptNormalizedDeterminant (m n : ℕ) (θ : ℝ) : ℂ :=
  manuscriptBoundaryDeterminant m n θ / manuscriptNormalizer m n θ

theorem manuscriptNormalizedDeterminant_real (m n : ℕ) (hm : 2 ≤ m) (θ : ℝ) :
    ((manuscriptNormalizedDeterminant m n θ).re : ℂ) = manuscriptNormalizedDeterminant m n θ := by
  apply Complex.conj_eq_iff_re.mp
  unfold manuscriptNormalizedDeterminant
  rw [map_div₀, manuscriptBoundaryDeterminant_conj m n hm,
    manuscriptNormalizer_conj m n hm]
  simp

theorem eigenvalue_iff_manuscriptNormalizedDeterminant_zero
    (m n : ℕ) (hm : 2 ≤ m) (θ : ℝ) (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    (∃ j : ℕ, 1 ≤ j ∧ j ≤ n ∧ eigenvalue m n j = symbol m θ) ↔
      manuscriptNormalizedDeterminant m n θ = 0 := by
  rw [eigenvalue_iff_manuscriptBoundaryDeterminant_zero m n hm θ hθ hθπ]
  simp only [manuscriptNormalizedDeterminant, div_eq_zero_iff,
    manuscriptNormalizer_ne_zero m n hm θ hθ hθπ.le, or_false]

#print axioms stableRootList_injective
#print axioms exteriorRootList_injective
#print axioms manuscriptPhaseProduct_contDiff
#print axioms manuscriptNormalizer_contDiff
#print axioms manuscriptNormalizer_ne_zero
#print axioms manuscriptNormalizer_conj
#print axioms manuscriptNormalizedDeterminant_real
#print axioms eigenvalue_iff_manuscriptNormalizedDeterminant_zero

end MF21Restart
