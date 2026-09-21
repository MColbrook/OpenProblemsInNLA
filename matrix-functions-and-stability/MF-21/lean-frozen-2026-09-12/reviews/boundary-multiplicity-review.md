# Independent boundary multiplicity review

Verdict: **APPROVE** for the five printed results and the actual restricted
linear map in `MF21Restart/BoundaryMultiplicity.lean`. The module proves
the dimension correspondence asserted after manuscript (13), lines
149–159. It supplies the kernel-dimension step used again in Lemma 4,
line 239. It does not by itself prove a simple determinant zero, a simple
spectral eigenvalue, phase indexing, or the complete MF-21 target.

I read the current source and statement lock independently, along with
the concrete boundary matrix and ghost interpretation, recurrence basis,
finite recurrence extension, and actual Fourier-to-matrix equation used
here. The unchanged definitions and imported proofs were checked at the
hashes listed below. No source was edited. This review applies the pinned
`REFEREE_STANDARDS.md` rubric, SHA256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Statement fidelity and the linear map

`boundaryInterior` (lines 15–23) is the actual complex-linear evaluation
map `c ↦ (j ↦ Σ_i c_i w_i^(m+j))`, with `j : Fin n`. Its coefficients are
given as a concrete matrix and its linearity comes from `mulVecLin`.
The shift m is exact: after shifting the manuscript's indices by m−1,
the lower ghosts are 0 through m−1, the interior is m through m+n−1,
and the upper ghosts are n+m through n+2m−1.

`toeplitz_eigen_equation_iff_finite_recurrence` (lines 25–46) is a
pointwise equivalence for arbitrary v, including zero. It uses the actual
integral-defined matrix and the existing convolution identity, whose
evenness step reconciles `a_(j-k)` with the matrix entry `a_(k-j)`. The
central recurrence sample is `k+m` and becomes `v k`. The coefficient
sign, endpoint division, and index conventions are unchanged.

The final source uses precisely the locked root hypotheses: `1 ≤ m`,
2m distinct nonzero complex numbers, and their actual Laurent spectral
equations at lam. No determinant criterion, kernel equivalence, matching
dimension, or surjectivity is assumed. `lam` may be any complex number;
the real eigenvalue application is a specialization. The actual root
list still has to be constructed before invoking this theorem.

## Injectivity and surjectivity are proved separately

`boundaryInterior_injective_on_kernel` (lines 48–73) uses equality of
the interior and both sets of zero ghosts to obtain equality of the
geometric sequences throughout `0 ≤ t < n+2m`. In particular they agree
at the first 2m indices. The transpose of the actual Vandermonde matrix
on the distinct roots is nonsingular, so their coefficient vectors are
equal. This proves injectivity of the evaluation map itself. It uses
only root distinctness, without a needless nonzero-root hypothesis at
shift zero. It does not infer injectivity from simultaneous nontriviality
of the two kernels.

`boundaryInterior_maps_to_eigenspace` (lines 75–105) derives the
characteristic-root equations of the actual order-2m Fourier recurrence,
then proves the coefficient-weighted geometric sequence satisfies that
recurrence. The ghost reconstruction theorem makes the zero extension
agree with the sequence on the whole required finite block. Every sample
in the equation at `k<n`, including `k+2m`, is strictly below n+2m.
This proves the literal Toeplitz eigenvector equation for the interior.
Distinctness is not needed for this direction and is correctly omitted.

`boundaryInterior_surjective_to_eigenspace` (lines 107–135) starts with
an arbitrary eigenvector, without assuming it nonzero. It takes the first
2m values of its zero ghost extension as initial data for Mathlib's
`mkSol`. The proved finite recurrence extension lemma shows agreement up
to n+2m. The geometric basis theorem supplies a coefficient vector for
this full recurrence solution. Agreement then gives both zero ghost
blocks and exactly the original interior vector. This is a direct proof
of surjectivity onto the eigenspace, including its zero vector.

`boundaryEigenspaceMap` (lines 137–147) restricts the actual linear
evaluation map to the boundary kernel and proves its image lies in the
actual eigenspace. Its additivity and scalar action are inherited from
that evaluation map; the scalar field is ℂ in both source and target.
`boundaryEigenspaceMap_bijective` (lines 149–164) applies the injectivity
and surjectivity just proved. Finally `boundary_kernel_finrank_eq_eigenspace`
(lines 166–174) constructs `LinearEquiv.ofBijective` from this map and
uses the library's dimension-invariance theorem. Thus the linear
equivalence actually exists in the proof, even though it is not given
an additional public definition name.

## Edge cases and limits

The proof covers `n<m`; the first 2m values may include part of the upper
ghost block, and the reconstruction theorem includes those positions.
When `n=0`, there is no interior, both ghost blocks together supply all
first 2m values, and the boundary matrix is Vandermonde. Both kernel and
eigenspace have dimension zero. No `n>0` premise conceals that case.
At `m=1,n=1,lam=2`, the distinct roots `i,-i` give a one-dimensional
boundary kernel and interior eigenspace, with the evaluated interior
nonzero on nonzero boundary-kernel vectors, as the theorem predicts.

At coalescing root parameters the distinctness premise fails; extending
the geometric basis through those parameters is not claimed. The result
proves equality of complex geometric dimensions. Deriving algebraic
multiplicity one from geometric multiplicity one for this Hermitian
matrix still uses its diagonalization/semisimplicity. Proving that
nullity at least two forces determinant derivative zero is a separate
matrix-calculus ingredient. Neither result is silently assumed in this
module, and neither phase ordering nor determinant normalization follows
from the dimension equality alone.

No custom axiom, placeholder, unsafe shortcut, `native_decide`, or
numerical certificate appears in the reviewed source. The computation
is symbolic finite-dimensional linear algebra. There is no material
correctness, hypothesis-strengthening, or source-fidelity finding.

## Execution evidence and exact scope

The coordinator reported the actual local `boundary-multiplicity-02`
run exited 0 at the source hash below. I read its log: all five printed
declarations depend only on `[propext, Classical.choice, Quot.sound]`.
I did not run Lean, another compiler, a test, a GitHub workflow, or
Comparator. The coordinator retains the serialized command and run
records; these local outputs are not represented as an independent
execution or a GitHub Comparator result. This is approval of the stated
mathematical ingredient, not a new completed original problem.

| File | SHA256 |
|---|---|
| `MF21Restart/BoundaryMultiplicity.lean` | `94d136b3310fe28699fa3a386143e2b22d20f23f226541aecc49468492d659b9` |
| `BOUNDARY_MULTIPLICITY_STATEMENTS.md` | `5301070cffef2747aa8596c64d081739550dc730f4233b6692d64aa03bce168f` |
| `MF21Restart/BoundaryToeplitz.lean` | `0e902d88e92b2609b159df07b118a7a4973607f2346687c6734ec47947369b19` |
| `MF21Restart/FiniteRecurrence.lean` | `a252b76405c506b2b850e288c41769083267a23a4e454c424096a6002e4db39a` |
| `MF21Restart/RecurrenceBasis.lean` | `ef4a5d7bbbb5db6e849ec6dbbc9289bda98300d7e1a7f78e47c26fd61457454b` |
| `MF21Restart/BoundaryRecurrence.lean` | `51605ff0487f4abd102ab9e6e755513adcbbf6c4df10007360227c3a3cf12f44` |
| `MF21Restart/Definitions.lean` | `35a74047a81a9b7526e9bf039880ca8f07ae33314e2b5b960ab254e02fca4b51` |
| `evidence/logs/boundary-multiplicity-02.log` | `fd22798eadeb7a26fcedf12bd8cd44fa4e60d3c64e1ec96b7632bdb034ed0e88` |
