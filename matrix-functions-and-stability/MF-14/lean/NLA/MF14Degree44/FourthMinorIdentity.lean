/- Exact unrestricted fourth-product determinant, using only small blocks.
Mathematical construction: Marcus Webb, The University of Manchester.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; substantial Codex assistance. -/
import NLA.MF14Degree44.FourthMinorBlocks

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.MF14Degree44

/-- D44-03d: exact polynomial certificate, valid also when s=0. -/
theorem fourth_minor_identity (alpha eta gamma s lam : ℂ) :
    (fourthJacobian alpha eta gamma s lam).det = fourthMinor alpha eta gamma s lam := by
  have hfirst := det_fin_add_of_lower_left_zero (m := 3) (n := 9)
    (fourthJacobian alpha eta gamma s lam)
    (fourth_first_lower_zero alpha eta gamma s lam)
  rw [fourth_first_block, Matrix.det_one, one_mul] at hfirst
  have hsecond := det_fin_add_of_lower_left_zero (m := 5) (n := 4)
    ((fourthJacobian alpha eta gamma s lam).submatrix (Fin.natAdd 3) (Fin.natAdd 3))
    (fourth_middle_lower_zero alpha eta gamma s lam)
  have h := hfirst.trans hsecond
  change (fourthJacobian alpha eta gamma s lam).det =
    ((fourthJacobian alpha eta gamma s lam).submatrix fourthCoreIndex fourthCoreIndex).det *
    ((fourthJacobian alpha eta gamma s lam).submatrix fourthTailIndex fourthTailIndex).det at h
  rw [fourth_core_matrix, fourth_core_det, fourth_tail_det] at h
  rw [h]
  unfold fourthMinor
  ring

#print axioms fourth_minor_identity
#assert_trust kernel fourth_minor_identity
end NLA.MF14Degree44
