# PR 307 audit: MI-18 order-four certificate

Audited head: `8a59a746c01273448875f61239d4481437b69590`.
Audit date: 2026-09-19. Auditor: separate Codex audit agent; this is AI review, not external human peer review or proof-assistant verification.

## Recommendation

Merge. No blocking mathematical, executable-code, artifact-integrity, or scope defect was found. No PR files required repair. The result covers every complex Hermitian PSD matrix of order four and all q in [-1,1], with strict monotonicity under positive diagonal and non-diagonality. The canonical arbitrary-order target and Partially resolved status remain intact.

## Review performed

- Read the complete proof, audit report, mathematical source, both executable verifiers, corruption harness, tensor addendum, certificate conventions, README, and canonical README/TeX diff.
- Inspected both ZIP member inventories before extraction: no absolute paths, traversal components, or symlinks; total uncompressed size bounded below 100 MB. Programs contain no network actions, dynamic execution, or unexpected external mutation. The corruption harness uses temporary files and invokes the two local verifiers. The addendum rewrites its generated JSON inside the extracted scratch package; its contents reproduce exactly.
- Extracted and read the complete six-page proof PDF; rendered and visually inspected all six proof pages, seven audit-report pages, and two canonical problem pages. No clipping, unreadable formulas, or content mismatch was found. Published proof/audit PDFs are byte-identical to the archive copies.
- Verified all 24 audited-package manifest entries and seven original-package entries; all retained original files are byte-identical, accounting for the documented README/manifest renames.
- Compared to the primary Mitchell paper, https://files.ele-math.com/articles/oam-14-56.pdf: its order-three complex Gram argument and fixed-first-vector singular reduction support the citations. A bounded fresh search for q-permanent monotonicity/order-four and Bapat/q-permanent/2026 found no overlapping result. This does not establish novelty or priority.

## Mathematical audit

1. The degree-five Bernstein reconstruction is valid for all derivative monomials of S4 (inversion lengths 0 through 6). Nonnegative Bernstein coefficients imply positivity over intervals, not merely at sampled q values. The intervals cover [-1,1] with no endpoint gap.
2. Contraction terms use conjugate-linear-first inner products correctly. Real symmetric PSD coefficient matrices define sums of squared norms for complex vectors. Scalar-pair terms have the requisite complex conjugates. Expansion uses all four distinct row and column indices; equality in all independent matrix-entry variables is stronger than an identity restricted to real matrices.
3. Reversal congruences and the D=diag(1,-1,1) sign/contraction exchange preserve PSD. The negative central interval is checked directly, with the sign twist used only for the contraction family that has no scalar blocks. No invalid general permutation invariance of q-permanents is assumed.
4. Near -1, the expectation of the weighted tensor-permutation operator is the q-permanent derivative. Inverse permutations have identical inversion lengths, making the operator Hermitian. The 81-dimensional tensor space over C3 splits exhaustively into the 15 multiplicity blocks; their dimensions and all 90 coefficient blocks are checked. Exact zero-pivot treatment covers rank-deficient matrices. The Schur-complement and real-symmetric characteristic-polynomial criteria are both mathematically sound.
5. Projection of the first Gram vector onto the other three changes only the first diagonal entry. Only permutations fixing that first index contribute to the difference, and their inversion count is preserved when it is deleted. This proves Pq(A)=Pq(A0)+||w||^2 Pq(B), with rank(A0)<=3, without an impermissible interior-index deletion or relabeling. The supplied three-vector SOS covers arbitrary complex parameters and all real q; zero first vectors are immediate, and positive first-vector rescaling is harmless. Thus rank four is covered as well.
6. The zero-diagonal boundary is allowed in the derivative theorem. Strictness correctly uses Hadamard's equality condition to show a positive-diagonal, non-diagonal PSD matrix yields a nonconstant polynomial. A nondecreasing polynomial cannot have a flat nontrivial interval unless it is constant. No claim that the derivative must be strictly positive pointwise is needed.
7. The optional symbol-merging intertwiners transfer positivity from six 12-dimensional representatives to other multiplicity types. This is separate from matrix-index relabeling. The main proof also checks all 90 blocks directly and does not depend on the addendum.

## Reproduction

Environment: Python 3.13.14, SymPy 1.14.0. Python is at `/tmp/pr-audit-20260919/agent-mi18/venv/bin/python`. Initial bundled/system runtimes lacked SymPy; the pinned dependency was installed only into this temporary environment.

All requested checks succeeded:

- `python check_certificate.py`: 18 exact 24-coefficient contraction identities; PSD by Schur complements and all principal minors; 90 exact tensor Bernstein PSD blocks; ranks [3,9,12,12,12,12]. See `original-verifier.log`.
- `python audit_verify.py --report .../reproduced-tensor-charpolys.json`: all whole-polynomial identities, all 66 stored small matrices PSD by characteristic polynomial, complex-conjugation identities, all 90 tensor blocks, entrywise reconstruction, rank reduction, arbitrary-complex order-three SOS, and strictness endpoint identities. See `second-verifier.log`.
- `python audit_mutations.py`: all twelve intended rejections (six corruptions x both implementations), with failures for the intended algebraic or data reasons. See `mutations.log`.
- `python tensor_addendum.py`: all 24 permutation intertwiners for each of three symbol-merging maps and all six factored characteristic polynomials. See `tensor-addendum.log`.
- Recomputed tensor records and six-block data exactly match package contents. See `integrity.log`.
- `python3 tools/validate_problem_ids.py --base-ref origin/main`: passed. See `problem-ids.log`.

## Limits

This audit checks the exact finite certificate and its mathematical correspondence; it is not a proof-assistant kernel check, a specialist's external peer review, or a certification of historical priority. The original proof and prior second implementation were produced by the same assistant, disclosed in the PR. This separate audit found no reason to reject the computer-assisted n=4 partial result. No claim for n>=5 follows from these data. Repository-wide catalog/CI checks and merge sequencing remain with the coordinating agent.
