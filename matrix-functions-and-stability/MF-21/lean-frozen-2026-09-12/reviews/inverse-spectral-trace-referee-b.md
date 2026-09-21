# Independent referee B: the actual finite inverse trace

Verdict: **APPROVE within the exact finite scope below.** I independently read the coordinator-authored final InverseSpectralTrace source, its prior statement lock, and the retained successful local evidence. I did not run Lean.

The reference is the frozen MF-21 manuscript, SHA-256 6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa, especially the trace sequence in (29) and the reciprocal sum passage preceding (31), lines 338-362. The review uses REFEREE_STANDARDS.md, SHA-256 e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1.

## Mathematical scope and fidelity

- posDef_inverse_trace proves the identity for a real positive-definite square matrix, not an assumed reciprocal trace. The actual Hermitian spectral theorem supplies unitary conjugation of a diagonal matrix. Positivity proves that every eigenvalue is nonzero; the reciprocal diagonal is explicitly shown to be a right inverse under that conjugation. Matrix.inv_eq_right_inv therefore identifies the actual matrix inverse. Trace cyclicity and the unitary identity remove the conjugation. This avoids treating a totalized inverse at zero as a genuine inverse without justification.
- sum_orderedEigenvalue_map proves invariance of the sum of an arbitrary real function under sorting the actual eigenvalue multiset. The List.ofFn/get identification and list permutation preserve every repeated eigenvalue. No simplicity, distinctness, chosen ordering convention, or permutation of a different matrix's spectrum is assumed.
- toeplitz_inverse_trace_ordered specializes the general result to the unchanged integral-defined toeplitz m n, using its proved positive definiteness for m>=1. The different proofs of Hermitian symmetry cause no change to the underlying proposition or spectrum.
- toeplitz_inverse_trace_one_based translates each i:Fin n to the original index i.val+1, explicitly proves 1<=i.val+1<=n, and applies the unchanged eigenvalue definition. Thus neither the first nor last eigenvalue is lost and no totalized out-of-range eigenvalue is used. For n=0 the sums and trace are empty, so the theorem remains meaningful and correct.

The m>=1 hypothesis is the natural positive-definiteness range used by the surrounding proof. All statements are finite equalities; there is no asymptotic assumption and no desired eigenvalue limit hidden in them.

This independent review covers the four new finite identities. It relies on the pinned Mathlib spectral theorem, the previously checked MatrixInverseAlgebra interface, and the actual positive-definiteness result in SpectralEnclosure. It does not represent this referee's earlier SpectralEnclosure proof as independently reviewed here; its separate independent review remains a dependency item.

## Exact source and evidence

I independently recomputed and matched all source/log/output hashes to the retained successful record:

- Source MF21Restart/InverseSpectralTrace.lean: 4cd1c1189a56438237db1f217bc6c3172032f955ff5d030f86cd7f4fd1129b1d.
- Prior lock INVERSE_SPECTRAL_TRACE_STATEMENTS.md: 396b56c44fc7dc453959812b0602c7e5cd86048bcf77aad93782f6496788dfda.
- Record evidence/logs/inverse-spectral-trace-03.json: d05be497c2bda01c4cb09dd89c5a0fe5a5739677f6276566cd6784685b1999c7.
- Log evidence/logs/inverse-spectral-trace-03.log: ec42e8ca806dc8d90ddcdf628ba7021139077e96ce14ac4bd8485fc925bf5078.
- Output .lake/build/lib/lean/MF21Restart/InverseSpectralTrace.olean: 212e9515f20f3997dbdc6a29a05d6b516cb3d50248a9841f5620d98fa3dcd701.

Recorded command in the MF21-restart working directory:

    env LEAN_NUM_THREADS=1 lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/InverseSpectralTrace.olean MF21Restart/InverseSpectralTrace.lean

The actual record reports exit_code=0 and source_unchanged=true. The log contains four axiom reports, each listing only propext, Classical.choice, and Quot.sound. No custom axiom, sorry, admit, unsafe shortcut, or numerical computation is present in this source.

This is source-matched coordinator local evidence inspected by the referee. It is not a referee compiler run or a GitHub Comparator run. The Tannery passage, fixed-index implication, full Target assembly, and final Comparator acceptance are outside this report's finite scope.

