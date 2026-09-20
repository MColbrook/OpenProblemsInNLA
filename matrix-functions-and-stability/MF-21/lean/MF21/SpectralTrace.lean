import MF21.ToeplitzGram

/-! The inverse trace is the sum of reciprocals of the actual eigenvalues
used in the MF-21 statement, including their specified increasing ordering. -/

open Matrix Finset
noncomputable section
namespace MF21Challenge

theorem positive_hermitian_inverse_trace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (hpos : ∀ j, 0 < hA.eigenvalues j) :
    A⁻¹.trace = ∑ j, (hA.eigenvalues j)⁻¹ := by
  let U : Matrix (Fin n) (Fin n) ℝ := hA.eigenvectorUnitary
  let e : Fin n → ℝ := hA.eigenvalues
  have hU : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hU' : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hspec : A = U * diagonal e * star U := by
    simpa only [Unitary.conjStarAlgAut_apply, Function.comp_def, RCLike.ofReal_real_eq_id,
      id_eq] using hA.spectral_theorem
  have hd : diagonal (fun j ↦ (e j)⁻¹) * diagonal e = 1 := by
    rw [diagonal_mul_diagonal]
    have he : (fun j ↦ (e j)⁻¹ * e j) = fun _ ↦ (1 : ℝ) := by
      funext j
      exact inv_mul_cancel₀ (ne_of_gt (hpos j))
    rw [he, diagonal_one]
  have hinv : A⁻¹ = U * diagonal (fun j ↦ (e j)⁻¹) * star U := by
    apply inv_eq_left_inv
    rw [hspec]
    calc
      _ = U * diagonal (fun j ↦ (e j)⁻¹) * (star U * U) * diagonal e * star U := by
        simp only [Matrix.mul_assoc]
      _ = U * (diagonal (fun j ↦ (e j)⁻¹) * diagonal e) * star U := by
        rw [hU, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hd, Matrix.mul_one, hU']
  rw [hinv, trace_mul_cycle, hU, Matrix.one_mul, trace_diagonal]

theorem toeplitz_inverse_trace (m n : ℕ) :
    (toeplitz m n)⁻¹.trace = ∑ j : Fin n, (eigenvalue m n j)⁻¹ := by
  let hA := toeplitz_isHermitian m n
  have hp : ∀ j, 0 < hA.eigenvalues j :=
    hA.posDef_iff_eigenvalues_pos.mp (toeplitz_posDef m n)
  rw [positive_hermitian_inverse_trace (toeplitz m n) hA hp]
  let E : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  have hE := E.symm.sum_comp (fun k ↦ (hA.eigenvalues₀ k)⁻¹)
  have hF := ((Fin.castOrderIso (Fintype.card_fin n).symm).toEquiv).sum_comp
    (fun k ↦ (hA.eigenvalues₀ k)⁻¹)
  have hR := Equiv.sum_comp Fin.revPerm
    (fun j : Fin n ↦ (hA.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm j))⁻¹)
  change (∑ j, (hA.eigenvalues j)⁻¹) =
    ∑ j : Fin n, (hA.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm j.rev))⁻¹
  simpa only [Matrix.IsHermitian.eigenvalues, E, Fin.revPerm_apply] using
    hE.trans (hF.symm.trans hR.symm)

end MF21Challenge

#print axioms MF21Challenge.positive_hermitian_inverse_trace
#print axioms MF21Challenge.toeplitz_inverse_trace
