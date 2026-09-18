/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi24_full_referee1.

Each actual compound norm is the product of the corresponding number of
largest positive eigenvalues. Apply the complete normalized norm inequality
in its genuine compound dimension. The determinant identity supplies equality
of the total products; dimensions and all closed parameter endpoints are retained.
-/
import NLA.MI28.CompoundTransport
import NLA.MI28.FullNorm
import NLA.MI28.NormalizedDeterminant

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI28

open NLA.MI24 (compoundMatrix compoundMatrix_posDef compound_dimensions)

lemma normalized_weak_log_majorized {n : ℕ} (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (k p : ℝ) (hk0 : 0 ≤ k)
    (hp0 : 0 ≤ p) (hp2 : p ≤ 2)
    (hH : (normalizedH A B k p).PosDef) (hZ : (normalizedZ A B k p).PosDef) :
    WeakLogMajorized (sortedSpectrum (normalizedH A B k p) hH)
      (sortedSpectrum (normalizedZ A B k p) hZ) := by
  intro j hj
  have hnorm := full_normalized_norm ((compound_dimensions n j).2 hj)
    (compoundMatrix j A) (compoundMatrix j B)
    (compoundMatrix_posDef j A hA) (compoundMatrix_posDef j B hB) k p hk0 hp0 hp2
  rw [← compound_normalizedH j A B hA hB, ← compound_normalizedZ j A B hA hB] at hnorm
  have hleft : operatorNorm (compoundMatrix j (normalizedH A B k p)) =
      prefixProduct (sortedSpectrum (normalizedH A B k p) hH) j hj :=
    NLA.MI24.infinitySchattenNorm_compound_eq_prefix j hj _ hH
  have hright : operatorNorm (compoundMatrix j (normalizedZ A B k p)) =
      prefixProduct (sortedSpectrum (normalizedZ A B k p) hZ) j hj :=
    NLA.MI24.infinitySchattenNorm_compound_eq_prefix j hj _ hZ
  rwa [hleft, hright] at hnorm

/-- C15: full complex log-majorization with actual positive-definiteness witnesses. -/
theorem full_log_majorization : FullLogMajorization := by
  intro n _ A B hA hB k p hk0 hp0 hp2
  obtain ⟨hH, hZ⟩ := normalized_posdef A B hA hB k p
  refine ⟨hH, hZ, normalized_weak_log_majorized A B hA hB k p hk0 hp0 hp2 hH hZ, ?_⟩
  rw [prod_sortedSpectrum_eq_det_re _ hH, prod_sortedSpectrum_eq_det_re _ hZ,
    normalized_determinants_eq A B hA hB]

end NLA.MI28
