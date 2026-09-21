# MF-21: formal verification of the frozen manuscript

The complete three-part MF-21 target and the manuscript's stronger smooth
coefficient theorem have passed local Lean checking. The proof manuscript
is unchanged. The final Linux Comparator check is recorded separately from
local compiler checks; see [VERIFICATION.md](VERIFICATION.md).

**George Stepaniants**  
Department of Computing and Mathematical Sciences, California Institute of
Technology. Developed with substantial AI assistance. Original mathematical
and library authorship is retained.

The main results are [`target_proved`](MF21Restart/TargetProof.lean) and
`manuscript_smooth_target`. For every integer `m ≥ 3`, one smooth coefficient
family satisfies all global expansion orders through `2m-1`, the critical
order on the exact logarithmic bulk range, and failure of a global critical
bound. The eigenvalues are those of the actual integral-defined Toeplitz
matrix, sorted with multiplicities and indexed by `1 ≤ j ≤ n`.

## Scope and source

The manuscript in [original-proof/solution.md](original-proof/solution.md)
is preserved byte for byte from commit
`eb37bc17a462177f57efa270e9a9f9b17e9d88e2`, SHA256
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`.
This is an independent formalization of that frozen manuscript. Existing
upstream MF-21 work and subsequent manuscript versions are separate. A second
formalization of MF-21 does not add another distinct solved problem.

The proof follows the boundary determinant, phase indexing, shared implicit
Taylor family, circulant interlacing, inverse-kernel limit, trace passage,
and irrationality contradiction. All required intermediate claims are proved;
there is no unproved spectral, Taylor, or kernel-limit premise in the target.
The inverse-kernel input is proved here from the actual finite inverse.

[STATEMENTS.md](STATEMENTS.md) and the component statement locks record the
statement-first development. [NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md)
explains the single closed LeanCert calculation, performed in kernel mode.
Parameter-dependent estimates are symbolic, without interval subdivision or
numerical matrix enumeration. The external proof of pi transcendence retains
its [authorship, license, and port provenance](vendor/gotrevor-pi/README.md).

## Reproduction and evidence

With the pinned dependency cache available, run:

```sh
python3 verify_local.py
```

This compiles the complete project serially, one Lean thread and at most
4096 MiB per process. It retains exact source, output and log hashes, commands,
exit codes and dependency revisions, and checks all 386 declarations in
Audit.lean against the three permitted standard axioms. A fresh installation
first needs its pinned dependencies and Mathlib cache materialized.

Seven separate Challenge/Solution contracts include the full canonical target
and the stronger smooth statement. Challenge contains deliberate theorem
placeholders and is never imported by Solution or a proof module. No definition
holes, proof-side sorries, custom axioms, or native-execution trust are used.
The [contract lock](COMPARATOR_TARGET_STATEMENTS.md) identifies the shared
definitions. A successful local compilation is not a Comparator run.

Independent agent reviews are in [reviews](reviews), using the pinned Tau Ceti
adaptation. Their exact source hashes, executed checks, author exclusions and
remaining external-check scopes are explicit. They are not human peer review.
The current evidence is summarized in [VERIFICATION.md](VERIFICATION.md);
failed and superseded development records are retained as history, not passes.
