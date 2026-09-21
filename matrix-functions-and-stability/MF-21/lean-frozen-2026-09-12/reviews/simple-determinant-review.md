# Independent simple determinant zero review

Verdict: **APPROVE**, for both results in `SimpleDeterminant.lean` at the
hash below. They prove complex geometric multiplicity one from an actual
simple boundary-determinant zero. They do not prove the existence or
location of such zeros, or algebraic multiplicity one.

Reviewer: `/root/mf21_restart_lean_audit`, 20 September 2026. I did not
author or edit this source. I read the complete module, its lock, its
two direct dependency sources, the manuscript passage, and the relevant
Mathlib finite-dimension and derivative-uniqueness statements. I ran no
compiler. The referee standard has SHA-256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Exact sources and local execution

Paths are relative to `MF21-restart`.

| Path | SHA-256 |
| --- | --- |
| `MF21Restart/SimpleDeterminant.lean` | `14221eca53ecb544043c81acffe32691f740afd2ffdeaa34c5fec4f2a6cfade1` |
| `SIMPLE_DETERMINANT_STATEMENTS.md` | `5a8a0afc174a011c6235d0367bda11de61196f13f201cac8652c65139726342b` |
| `MF21Restart/DeterminantMultiplicity.lean` | `fab853f9067b237317147e006d42860889ef6a819c0cd500ca5cf85ed59bf7cb` |
| `MF21Restart/BoundaryMultiplicity.lean` | `94d136b3310fe28699fa3a386143e2b22d20f23f226541aecc49468492d659b9` |
| `original-proof/solution.md` | `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa` |
| `evidence/logs/simple-determinant-01.json` | `56b65eeb34330d64bcf4e7fdc17dd966186f0204d33e8ac959356f61bbfcbbc9` |
| `evidence/logs/simple-determinant-01.log` | `94f16da31257aa4754526d6b125e495ac16d160a6e0d431786002bfc027f1acf` |
| `.lake/build/lib/lean/MF21Restart/SimpleDeterminant.olean` | `b74506804f86eb2d0c9c7665f82fe2eeb8caac887df011d0c7b20a50d2d49234` |

The individual execution record reports an actual local run from
`2026-09-20T20:20:30.156976+00:00` to
`2026-09-20T20:20:36.326267+00:00`, with `LEAN_NUM_THREADS=1`, command

```text
lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/SimpleDeterminant.olean MF21Restart/SimpleDeterminant.lean
```

and exit code 0. I independently hashed the current source, log, and
compiled artifact: each equals its recorded hash. Both printed theorems
have exactly `propext`, `Classical.choice`, and `Quot.sound`. The record
explicitly says `comparator: not_run`; no GitHub Comparator or independent
compiler execution by this reviewer is claimed.

## Exact general theorem and proof

Lines 9–15 concern an arbitrary real-parameter complex square matrix
curve. They assume its actual matrix derivative, the actual determinant
derivative d, `d != 0`, and determinant value zero. The conclusion is
complex kernel dimension exactly one. The proof does not assume the
kernel is one-dimensional or that the matrix rank is N−1.

Lines 16–22 use determinant zero to obtain a nonzero vector killed by
the actual matrix, retain nonzeroness when passing to the kernel
subtype, and conclude strictly positive finite dimension. Lines 23–27
exclude dimension at least two using the previously proved determinant
derivative theorem and uniqueness of derivatives. This yields d=0 and
contradicts the genuine simple-zero hypothesis. Natural arithmetic then
gives dimension one. Both the lower and upper dimension bounds are
necessary: omitting determinant zero would allow invertible matrices,
and omitting d!=0 would allow larger kernels.

These are ordinary realizable hypotheses. The scalar curve `[t]` at
zero has d=1 and kernel dimension one. More generally, `diag(t,1,...,1)`
has the same behavior. At N=0 the zero-determinant premise is impossible,
which is coherent because the empty determinant is one. No broad
vacuity or contradictory global limit assumption appears.

## Actual Toeplitz eigenspace specialization

Lines 30–43 specialize this result to `boundaryMatrix m n (w t)`, with
the same matrix in both derivative hypotheses and the zero-value
hypothesis. The root conditions are required only at the point θ:
exactly 2m distinct, nonzero roots of the actual Laurent spectral
equation. The assumption `1 <= m` supplies the Fourier recurrence's
nonzero endpoint normalization. No assumed multiplicity equality is
introduced.

At line 41, the previously proved boundary-kernel/eigenspace dimension
identity replaces the target dimension. Its target is literally
`Module.End.eigenspace ((toeplitz m n).map Complex.ofReal).mulVecLin lam`,
with complex scalars, so this is the actual complexified integral-defined
Toeplitz matrix. The proof then applies the general theorem to the
literal boundary matrix curve. A spectral identity in a neighborhood
of θ is not needed for this local dimension inference.

I also inspected the current `BoundaryMultiplicity.lean` dependency:
its interior map evaluates the actual geometric sequence at indices
`m+j`; injectivity on the boundary kernel follows from the two ghost
blocks and the Vandermonde matrix, while surjectivity follows from the
finite recurrence extension and geometric basis. The dimension equality
comes from a constructed bijective complex-linear map. It is not
inferred merely from simultaneous nontriviality. The separate independent
`boundary-multiplicity-review.md` covers that dependency in full.

This matches `original-proof/solution.md:239`, precisely the geometric
dimension argument in Lemma 4. The hypotheses are conditional on a valid
root list and a simple zero, as the lock explicitly states. Construction
of the concrete root list and its smoothness occurs in separate modules;
the analytic estimates that will establish simple zeros are not hidden
in the proof of the dimension inference.

## Trust and limits

No `sorry`, `admit`, custom axiom, unsafe shortcut, `native_decide`, legacy
import, or Challenge import appears. The proof uses symbolic linear
algebra and derivative uniqueness; it has no numerical computation or
LeanCert requirement. The ordinary imported Fourier and recurrence
lemmas are genuine proofs and are visible in the dependency review.

No material correctness or source-fidelity change is requested. The
result concerns **geometric multiplicity over ℂ**. Algebraic simplicity
uses a further diagonalizability or Hermitian-spectrum argument, and
proving nonzero determinant derivatives uses the outstanding analytic
work. The theorem does not establish phase indexing, uniform remainder
bounds, or the complete MF-21 Target, and it does not add a completed
original problem.
