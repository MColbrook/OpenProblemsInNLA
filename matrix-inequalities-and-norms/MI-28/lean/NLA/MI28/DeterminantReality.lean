/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

The two determinant factorizations have positive real factors. This proves
both reality and strict positivity in the complex scalar order, without
claiming that the original right-hand sum is Hermitian.
-/
import NLA.MI28.DeterminantNormalization

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI28

/-- C19: actual complex determinants have zero imaginary part and positive real part. -/
theorem determinant_reality_positive {n : ℕ} (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (k p : ℝ) :
    (determinantLeft A B k p).im = 0 ∧ (determinantRight A B k p).im = 0 ∧
    0 < (determinantLeft A B k p).re ∧ 0 < (determinantRight A B k p).re := by
  have hnorm := determinant_normalization A B hA hB k p
  have hpd := normalized_posdef A B hA hB k p
  have hAk : (spectralPower A k).PosDef := NLA.MI24.spectralPower_posDef A hA k
  have hH : (1 + normalizedH A B k p).PosDef := Matrix.PosDef.one.add hpd.1
  have hZ : (1 + normalizedZ A B k p).PosDef := Matrix.PosDef.one.add hpd.2
  have hleft : 0 < determinantLeft A B k p := by
    rw [hnorm.2]
    exact mul_pos hAk.det_pos hZ.det_pos
  have hright : 0 < determinantRight A B k p := by
    rw [hnorm.1]
    exact mul_pos hAk.det_pos hH.det_pos
  exact ⟨(Complex.pos_iff.mp hleft).2.symm, (Complex.pos_iff.mp hright).2.symm,
    (Complex.pos_iff.mp hleft).1, (Complex.pos_iff.mp hright).1⟩

end NLA.MI28
