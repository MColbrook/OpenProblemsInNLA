# Referee B: actual weighted Toeplitz factorization

Verdict: **APPROVE**, scoped to `toeplitz_weighted_factorization` in
`MF21Restart/ToeplitzWeightedFactorization.lean`. The reviewer did not
author or edit this module and ran no compiler. The exact finite identity
is reviewed here; no uniform kernel convergence or MF-21 completion is
claimed.

## Frozen source and evidence

| Item | SHA-256 |
| --- | --- |
| `MF21Restart/ToeplitzWeightedFactorization.lean` | `ce4688dbb33b3482e6fc22315cc4b9cff3aa31fa491bfa018cd5f86e71d32a5e` |
| `TOEPLITZ_WEIGHTED_FACTORIZATION_STATEMENTS.md` | `c5d9a998c0ec95dc538c36b99d2666df2424c2a7039edb78a26343fb60740f02` |
| `evidence/logs/toeplitz-weighted-factorization-02.json` | `b011af95c6a4982add832164b8fa58379bb5df5408c07c58975706c62d56c810` |
| `evidence/logs/toeplitz-weighted-factorization-02.log` | `b258355538d95430fa2739ffca61059132a010b080661bb940265b6dfec8e9c5` |
| `.lake/build/lib/lean/MF21Restart/ToeplitzWeightedFactorization.olean` | `800f5dc13a074d11fcafa7a3cd1a8a54d534fa4906f828d5e618a5420652892d` |

The reviewer recomputed source, log, and output hashes and matched them
to the retained JSON. It records unchanged source, exit code 0,
`LEAN_NUM_THREADS=1`, and

```
lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/ToeplitzWeightedFactorization.olean MF21Restart/ToeplitzWeightedFactorization.lean
```

The observed theorem report lists only `propext`, `Classical.choice`,
and `Quot.sound`. These are local development records; no Comparator
check is claimed. The manuscript and pinned referee-rubric hashes are
respectively `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`
and `e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Mathematical and statement review

The diagonal at line 23 evaluates the rising factorial at `i.val+1`.
This is the positive one-based argument; it does not evaluate at a
zero factor or silently use descending factorials. The helper immediately
below identifies it with the corresponding natural ascending factorial.

The private Fourier helper derives
`fourierCoeff m d = (-1)^d * choose(2*m,m+d)` for natural `d` from
the previously proved actual integral-coefficient formula. It handles
both `d<=m` and `d>m`: in the latter case the actual Fourier support
theorem and the out-of-range binomial coefficient both give zero. The
sign reduction removes an even `2*m`, not an unsupported negative
natural exponent.

The Gram expansion uses `T.transpose*W*T`, so its summation entries
are `T(k,i)*W(k,k)*T(k,j)`. For `j<=i`, restricting to `k<=j` is
valid because the second upper-triangular factor is zero otherwise;
inside that range the first triangular factor is valid too. The
explicit bijection `k ↦ k.val+1` gives precisely the positive range
`1,...,j.val+1`, and the inverse is proved to remain in `Fin n`.
The sign identity
`(i-k)+(j-k)=(i-j)+2*(j-k)` is used only under `k<=j<=i`, where
every natural subtraction has its intended value.

The public proof applies the already-proved weighted binomial identity
with displacement `i-j` and positive index `j+1`. This gives exactly
the two diagonal weights `(j+1)_m` and `(i+1)_m` times
`choose(2*m,m+i-j)`. The integral Fourier helper supplies the remaining
sign. There is no altered Toeplitz definition, inverse hypothesis, or
limit assumption. The remaining matrix half is obtained by symmetry
of this real weighted Gram expression and the actual theorem
`fourierCoeff_neg`, with scalar factors reordered only inside real
entries.

The resulting identity is the literal locked `T^T W T=P A P` for the
actual `toeplitz m n`, for every `m>=1` and all `n`, including zero.
As an algebraic orientation check, at `m=1,n=2`, the left side is
`[[2,-2],[-2,8]]`; the right side uses `P=diag(1,2)` and
`A=[[2,-1],[-1,2]]` and agrees. This was a hand calculation, not an
additional executed numerical or Lean test.

No material issue was found. The triangular inverse and Fourier
binomial bridge have separate independent reviews by this referee.
The weighted binomial identity itself is a previously proved imported
dependency, with a separate coordinator review; this report checks
its use and index substitution, not a new review of its full proof.
This finite identity is appropriate algebra toward the cited inverse
input in manuscript Section 5. Actual inverse entries and their
uniform scaled limit remain separate statements.
