# Referee B: generic finite inverse algebra

Verdict: **APPROVE**, scoped to the four printed declarations in
`MF21Restart/MatrixInverseAlgebra.lean`. The reviewer did not author or
edit the source and ran no compiler. This is a generic matrix identity;
its explicit factorization premises still require proof in an application
to the actual Toeplitz matrix.

## Frozen source and evidence

| Item | SHA-256 |
| --- | --- |
| `MF21Restart/MatrixInverseAlgebra.lean` | `c8875cd75561ef852fa151509ad848659a04fdc8d758c358861a8abe41fe95d3` |
| `MATRIX_INVERSE_ALGEBRA_STATEMENTS.md` | `9cd0f449de998bb7d558814a3a52eb0c607e4297c44021c224fc3205bb18a02b` |
| `evidence/logs/matrix-inverse-algebra-02.json` | `45c5343e24049ab439b80cf22f45294cbac483f7f40bcb0db28fbe7a0fff7f00` |
| `evidence/logs/matrix-inverse-algebra-02.log` | `bf45f8662838aec3a47b518f131db5834f57c6406db717cfdff4d07cc8da164c` |
| `.lake/build/lib/lean/MF21Restart/MatrixInverseAlgebra.olean` | `54999a411e4a3ba91614d601e65754b823d1cc1d0dca283fac4d9575a1b9ffdb` |

The reviewer recomputed source, log, and output hashes and matched them
to the retained JSON. It records unchanged source, exit code 0,
`LEAN_NUM_THREADS=1`, and

```
lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/MatrixInverseAlgebra.olean MF21Restart/MatrixInverseAlgebra.lean
```

The observed log lists only `propext`, `Classical.choice`, and
`Quot.sound` for all four declarations. These are actual local records;
no Comparator or unrun independent compiler check is claimed. The
manuscript and pinned referee-rubric hashes are respectively
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`
and `e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Mathematical review

The two diagonal identities use pointwise nonvanishing to justify
reciprocals and prove both multiplication orders. They require no
positivity or nonempty index type; zero diagonal entries are excluded
exactly where needed.

`rightInverse_of_weighted_factorization` uses the locked five finite
identities with the correct multiplication order. Inserting `R*P=1`
on the left gives `R*(P*A*P)*B*V*B.transpose*P`. Substituting the
factorization cancels `T*B`, then `W*V`, then
`T.transpose*B.transpose=(B*T).transpose`, leaving `R*P=1`. Neither
commutativity of matrix multiplication nor a symmetry assumption on
`P` or `A` is used. The equality `P*A*P`, rather than `P.transpose*A*P`,
is deliberate and is exactly the prior lock. Its concrete application
must establish that exact identity.

`inverse_of_weighted_factorization` then uses Mathlib's
`Matrix.inv_eq_right_inv`. Thus the conclusion uses Mathlib's actual
nonsingular inverse, whose singular value is totalized; it does not
introduce a new inverse definition or assume determinant nonvanishing.
The exhibited right inverse establishes the needed invertibility. The
empty finite index type is valid as well.

No material issue was found. Requiring both `T*B=1` and `B*T=1` is
algebraically redundant for these finite square matrices, but it matches
the already-proved two-sided triangular identities and makes the exact
transpose cancellation transparent. This is optional simplification,
not a stronger unresolved application premise. There is no numerical
enumeration, new custom axiom, or hidden spectral assumption. No actual
Toeplitz inverse formula, kernel limit, trace limit, or original-target
completion follows from this generic module alone.
