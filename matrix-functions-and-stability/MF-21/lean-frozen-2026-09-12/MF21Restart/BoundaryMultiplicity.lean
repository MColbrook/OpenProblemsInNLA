import MF21Restart.BoundaryToeplitz
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The actual boundary kernel and Toeplitz eigenspace are linearly
equivalent, not merely simultaneously nontrivial. -/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators

namespace MF21Restart

def boundaryInterior (m n : ℕ) (w : Fin (2 * m) → ℂ) :
    (Fin (2 * m) → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  (Matrix.of (fun j : Fin n => fun i : Fin (2 * m) =>
    w i ^ (m + j.val))).mulVecLin

lemma boundaryInterior_apply (m n : ℕ) (w c : Fin (2 * m) → ℂ) (j : Fin n) :
    boundaryInterior m n w c j = ∑ i, c i * w i ^ (m + j.val) := by
  simp only [boundaryInterior, Matrix.mulVecLin_apply, Matrix.mulVec,
    dotProduct, Matrix.of_apply, mul_comm]

lemma toeplitz_eigen_equation_iff_finite_recurrence
    (m n : ℕ) (hm : 1 ≤ m) (lam : ℂ) (v : Fin n → ℂ) :
    (toeplitz m n).map Complex.ofReal *ᵥ v = lam • v ↔
      ∀ k : Fin n, zeroGhostExtension m n v (k.val + 2 * m) =
        ∑ i, (fourierRecurrence m lam).coeffs i *
          zeroGhostExtension m n v (k.val + i.val) := by
  constructor
  · intro hvec k
    apply (fourierRecurrence_equation_iff m hm lam
      (zeroGhostExtension m n v) k.val).mpr
    rw [zeroGhost_convolution_eq_toeplitz_mulVec]
    have hmid : zeroGhostExtension m n v (k.val + m) = v k := by
      simpa only [Nat.add_comm] using zeroGhostExtension_middle m n v k
    simpa only [hmid, Pi.smul_apply, smul_eq_mul] using congrFun hvec k
  · intro hrec
    funext k
    have hk := (fourierRecurrence_equation_iff m hm lam
      (zeroGhostExtension m n v) k.val).mp (hrec k)
    rw [zeroGhost_convolution_eq_toeplitz_mulVec] at hk
    have hmid : zeroGhostExtension m n v (k.val + m) = v k := by
      simpa only [Nat.add_comm] using zeroGhostExtension_middle m n v k
    simpa only [hmid, Pi.smul_apply, smul_eq_mul] using hk

theorem boundaryInterior_injective_on_kernel
    (m n : ℕ) (w : Fin (2 * m) → ℂ) (hinj : Function.Injective w)
    (c d : Fin (2 * m) → ℂ)
    (hc : boundaryMatrix m n w *ᵥ c = 0)
    (hd : boundaryMatrix m n w *ᵥ d = 0)
    (hmid : boundaryInterior m n w c = boundaryInterior m n w d) : c = d := by
  have hgc := (boundary_mulVec_zero_iff_ghosts m n w c).mp hc
  have hgd := (boundary_mulVec_zero_iff_ghosts m n w d).mp hd
  have heqc := zeroGhostExtension_eq_of_ghosts m n
    (fun k => ∑ i, c i * w i ^ k) hgc.1 hgc.2
  have heqd := zeroGhostExtension_eq_of_ghosts m n
    (fun k => ∑ i, d i * w i ^ k) hgd.1 hgd.2
  have hmid' : (fun j : Fin n => ∑ i, c i * w i ^ (m + j.val)) =
      (fun j : Fin n => ∑ i, d i * w i ^ (m + j.val)) := by
    simpa only [funext_iff, boundaryInterior_apply] using congrFun hmid
  let V := (Matrix.vandermonde w).transpose
  have hdet : V.det ≠ 0 := by
    simpa only [V, Matrix.det_transpose] using Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  apply Matrix.mulVec_injective_of_det_ne_zero hdet
  funext k
  have h1 := heqc k.val (by omega)
  have h2 := heqd k.val (by omega)
  rw [hmid'] at h1
  have heq := h1.symm.trans h2
  simpa only [V, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Matrix.vandermonde_apply, mul_comm] using heq

theorem boundaryInterior_maps_to_eigenspace
    (m n : ℕ) (hm : 1 ≤ m) (lam : ℂ) (w : Fin (2 * m) → ℂ)
    (hnonzero : ∀ i, w i ≠ 0)
    (hvalue : ∀ i, (2 - w i - (w i)⁻¹) ^ m = lam)
    (c : Fin (2 * m) → ℂ) (hc : boundaryMatrix m n w *ᵥ c = 0) :
    (toeplitz m n).map Complex.ofReal *ᵥ boundaryInterior m n w c =
      lam • boundaryInterior m n w c := by
  let u : ℕ → ℂ := fun k => ∑ i, c i * w i ^ k
  have hroot : ∀ i, (fourierRecurrence m lam).charPoly.IsRoot (w i) :=
    fun i => fourierRecurrence_charPoly_isRoot m hm lam (w i) (hnonzero i) (hvalue i)
  have hu : (fourierRecurrence m lam).IsSolution u :=
    geometric_sum_isSolution (fourierRecurrence m lam) w c hroot
  have hg := (boundary_mulVec_zero_iff_ghosts m n w c).mp hc
  have heq : ∀ t < n + 2 * m,
      zeroGhostExtension m n (boundaryInterior m n w c) t = u t := by
    have hfun : (fun j : Fin n => u (m + j.val)) = boundaryInterior m n w c := by
      funext j
      exact (boundaryInterior_apply m n w c j).symm
    have h := zeroGhostExtension_eq_of_ghosts m n u hg.1 hg.2
    rw [hfun] at h
    exact h
  apply (toeplitz_eigen_equation_iff_finite_recurrence m n hm lam _).mpr
  intro k
  rw [heq (k.val + 2 * m) (by omega)]
  calc
    u (k.val + 2 * m) =
        ∑ i, (fourierRecurrence m lam).coeffs i * u (k.val + i.val) := hu k.val
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [heq (k.val + i.val) (by have := i.isLt; change i.val < 2 * m at this; omega)]

theorem boundaryInterior_surjective_to_eigenspace
    (m n : ℕ) (hm : 1 ≤ m) (lam : ℂ) (w : Fin (2 * m) → ℂ)
    (hinj : Function.Injective w) (hnonzero : ∀ i, w i ≠ 0)
    (hvalue : ∀ i, (2 - w i - (w i)⁻¹) ^ m = lam)
    (v : Fin n → ℂ) (hv : (toeplitz m n).map Complex.ofReal *ᵥ v = lam • v) :
    ∃ c : Fin (2 * m) → ℂ, boundaryMatrix m n w *ᵥ c = 0 ∧
      boundaryInterior m n w c = v := by
  let E := LinearRecurrence.mk (2 * m) (fourierRecurrence m lam).coeffs
  let u := E.mkSol (fun i => zeroGhostExtension m n v i.val)
  have hrec := (toeplitz_eigen_equation_iff_finite_recurrence m n hm lam v).mp hv
  have heq : ∀ t < n + 2 * m, u t = zeroGhostExtension m n v t := by
    apply mkSol_eq_of_finite_recurrence E n (zeroGhostExtension m n v)
    intro k hk
    exact hrec ⟨k, hk⟩
  have hroot : ∀ i, E.charPoly.IsRoot (w i) :=
    fun i => fourierRecurrence_charPoly_isRoot m hm lam (w i) (hnonzero i) (hvalue i)
  obtain ⟨c, hc, _⟩ := recurrence_solution_geometric_basis E w hinj hroot u
    (E.is_sol_mkSol _)
  refine ⟨c, (boundary_mulVec_zero_iff_ghosts m n w c).mpr ?_, ?_⟩
  · constructor
    · intro k
      rw [← hc k.val, heq k.val (by omega)]
      exact zeroGhostExtension_lower m n v k
    · intro k
      rw [← hc (n + m + k.val), heq (n + m + k.val) (by omega)]
      exact zeroGhostExtension_upper m n v k
  · funext j
    rw [boundaryInterior_apply, ← hc (m + j.val), heq (m + j.val) (by omega)]
    exact zeroGhostExtension_middle m n v j

def boundaryEigenspaceMap
    (m n : ℕ) (hm : 1 ≤ m) (lam : ℂ) (w : Fin (2 * m) → ℂ)
    (hnonzero : ∀ i, w i ≠ 0)
    (hvalue : ∀ i, (2 - w i - (w i)⁻¹) ^ m = lam) :
    LinearMap.ker (boundaryMatrix m n w).mulVecLin →ₗ[ℂ]
      Module.End.eigenspace ((toeplitz m n).map Complex.ofReal).mulVecLin lam :=
  { toFun := fun c => ⟨boundaryInterior m n w c,
      Module.End.mem_eigenspace_iff.mpr
        (boundaryInterior_maps_to_eigenspace m n hm lam w hnonzero hvalue c c.property)⟩
    map_add' := by intro c d; apply Subtype.ext; exact map_add (boundaryInterior m n w) c.val d.val
    map_smul' := by intro a c; apply Subtype.ext; exact map_smul (boundaryInterior m n w) a c.val }

theorem boundaryEigenspaceMap_bijective
    (m n : ℕ) (hm : 1 ≤ m) (lam : ℂ) (w : Fin (2 * m) → ℂ)
    (hinj : Function.Injective w) (hnonzero : ∀ i, w i ≠ 0)
    (hvalue : ∀ i, (2 - w i - (w i)⁻¹) ^ m = lam) :
    Function.Bijective (boundaryEigenspaceMap m n hm lam w hnonzero hvalue) := by
  constructor
  · intro c d h
    apply Subtype.ext
    exact boundaryInterior_injective_on_kernel m n w hinj c d c.property d.property
      (congrArg Subtype.val h)
  · intro v
    obtain ⟨c, hc, hv⟩ := boundaryInterior_surjective_to_eigenspace
      m n hm lam w hinj hnonzero hvalue v
      (Module.End.mem_eigenspace_iff.mp v.property)
    refine ⟨⟨c, hc⟩, ?_⟩
    exact Subtype.ext hv

theorem boundary_kernel_finrank_eq_eigenspace
    (m n : ℕ) (hm : 1 ≤ m) (lam : ℂ) (w : Fin (2 * m) → ℂ)
    (hinj : Function.Injective w) (hnonzero : ∀ i, w i ≠ 0)
    (hvalue : ∀ i, (2 - w i - (w i)⁻¹) ^ m = lam) :
    Module.finrank ℂ (LinearMap.ker (boundaryMatrix m n w).mulVecLin) =
      Module.finrank ℂ
        (Module.End.eigenspace ((toeplitz m n).map Complex.ofReal).mulVecLin lam) :=
  (LinearEquiv.ofBijective (boundaryEigenspaceMap m n hm lam w hnonzero hvalue)
    (boundaryEigenspaceMap_bijective m n hm lam w hinj hnonzero hvalue)).finrank_eq

#print axioms boundaryInterior_injective_on_kernel
#print axioms boundaryInterior_maps_to_eigenspace
#print axioms boundaryInterior_surjective_to_eigenspace
#print axioms boundaryEigenspaceMap_bijective
#print axioms boundary_kernel_finrank_eq_eigenspace

end MF21Restart
