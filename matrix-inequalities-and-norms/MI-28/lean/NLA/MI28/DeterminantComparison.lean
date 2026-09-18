/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

The original complex determinant target follows from full log-majorization,
the proved scalar product transfer, and exact normalization. C19 supplies both
imaginary-part equalities explicitly. No Hermitian property of the original
right-hand sum, literature inequality, or target conclusion is assumed.
-/
import NLA.MI28.FullLogMajorization
import NLA.MI28.ProductOneAdd
import NLA.MI28.DeterminantReality

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI28

/-- C20: the complete unchanged canonical determinant inequality. -/
theorem determinant_comparison : DeterminantComparison := by
  intro n hn A B hA hB k p hk0 hp0 hp2
  obtain ⟨hH, hZ, hlog⟩ := full_log_majorization n hn A B hA hB k p hk0 hp0 hp2
  have hprod := product_one_add_le
    (sortedSpectrum (normalizedH A B k p) hH) (sortedSpectrum (normalizedZ A B k p) hZ)
    (NLA.MI24.sortedSpectrum_pos _ hH) (NLA.MI24.sortedSpectrum_pos _ hZ)
    (NLA.MI24.sortedSpectrum_antitone _ hH) hlog.1
  have hdet : Matrix.det (1 + normalizedH A B k p) ≤
      Matrix.det (1 + normalizedZ A B k p) := by
    rw [det_one_add_eq_prod_sortedSpectrum _ hH, det_one_add_eq_prod_sortedSpectrum _ hZ]
    exact_mod_cast hprod
  have hAk : (spectralPower A k).PosDef := NLA.MI24.spectralPower_posDef A hA k
  have hscaled := mul_le_mul_of_nonneg_left hdet hAk.det_pos.le
  have hnorm := determinant_normalization A B hA hB k p
  rw [← hnorm.1, ← hnorm.2] at hscaled
  have hreal := determinant_reality_positive A B hA hB k p
  exact ⟨hreal.1, hreal.2.1, (Complex.le_def.mp hscaled).1⟩

#print axioms determinant_comparison
#assert_trust kernel determinant_comparison

end NLA.MI28
