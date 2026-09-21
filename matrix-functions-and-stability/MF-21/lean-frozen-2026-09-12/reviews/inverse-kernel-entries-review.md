# Independent review: exact rising-factorial entries and reversal

Verdict: **APPROVE** the four stated finite identities. They rewrite the
actual inverse into the correctly normalized rising-factorial sum and
prove the exact discrete reversal symmetry. They assert no kernel limit.

Reviewer: `/root/mf21_restart_lean_audit`, 20 September 2026. The coordinator
authored this source; the reviewer made no source edits and ran no compiler.
The pinned standards have SHA256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Exact source and actual local evidence

| Artifact | SHA256 |
|---|---|
| `MF21Restart/InverseKernelEntries.lean` | `2c465270d2bc5d484c19b911cea95936ebdb873eb81edf6d96b35054c9d517bc` |
| `INVERSE_KERNEL_ENTRIES_STATEMENTS.md` | `958d0702e74cce4c1bf4324231003ad3551bacf9ba69a5dea9d695252abb819c` |
| `evidence/logs/inverse-kernel-entries-01.json` | `1ea37d9cef98041e9afb41dbe801a74922de6b1f95be67cba193cc5ae1eac0e6` |
| `evidence/logs/inverse-kernel-entries-01.log` | `06914d3f6c1e717730c44e04238b8321459d91b81dad6d5f7896adb327978198` |
| `.lake/build/lib/lean/MF21Restart/InverseKernelEntries.olean` | `33f04b3b000faf36600b92665a5d91b163b9910151cc41a8ca97d0086640fff1` |

The reviewer independently recomputed these hashes and matched the actual
01 record to the current source/log/output. It records exit_code=0,
source_unchanged=true, `LEAN_NUM_THREADS=1`, and
`lake env lean -j1 -M4096 -o
.lake/build/lib/lean/MF21Restart/InverseKernelEntries.olean
MF21Restart/InverseKernelEntries.lean`. All four printed declarations
depend only on `propext`, `Classical.choice`, and `Quot.sound`, with no
error line or `sorryAx`. No Comparator run is claimed.

## Mathematical and convention checks

1. At lines 13–23, the identity
   `choose(r+d,r)=(d+1)_r/r!` is derived from the existing natural
   ascending-factorial formula. The denominator r! is explicitly
   nonzero before division. The lemma covers r=0, where both sides
   equal one, and every natural d. No asymptotic factorial replacement
   or approximate Gamma identity is used.

2. At lines 25–44, each of the two binomial factors in the actual finite
   inverse is replaced by its exact rising-factorial expression. The
   resulting common factor is
   `(i+1)_m*(j+1)_m/((m-1)!)^2`, with the square of the factorial in the
   denominator. The summand has the two order m-1 rises beginning at
   k-i+1 and k-j+1, and the order 2m denominator beginning at k+1.
   This matches the known finite Duduchava–Roch formula recorded in
   `INVERSE_KERNEL_RESEARCH.md` after translating zero-based Fin indices
   to the one-based positive arguments. It is not a new mathematical
   attribution.

3. Both guards `i.val<=k.val` and `j.val<=k.val` remain in the sum.
   Thus the natural subtractions represent actual nonnegative offsets
   exactly where a term contributes. The summation range is the whole
   `Fin n`, with all terms below max(i,j) zero; no last term or diagonal
   term is lost. At m=1, the order m-1 factors are order zero and the
   factorial denominator is 0! squared, so the formula includes that
   boundary case without a new convention. All n are included; n=0 has
   no entries. This theorem concerns the actual `(toeplitz m n)⁻¹`
   from `ToeplitzInverse.lean`, not a separately defined candidate.

4. At lines 46–55, simultaneous row and column reversal changes the
   integer frequency i-j to its negative. The bounds i.val<n and
   j.val<n justify rewriting the reversed natural indices before
   casting their difference to integers. `fourierCoeff_neg` then proves
   the symmetry directly from the original even Fourier coefficient.
   No binomial formula or assumed centrosymmetry is required.

5. At lines 57–62, the exact matrix symmetry is transferred through
   `Matrix.inv_submatrix_equiv` for the two reversal permutations.
   This gives the true inverse entry at `(i.rev,j.rev)` equal to the
   entry at `(i,j)`. The theorem correctly covers every m,n; it does
   not infer inverse equivariance from pointwise candidate formulas or
   assume a nonzero determinant unnecessarily.

The discrete reversal is i.val -> n-1-i.val, equivalently the one-based
index i -> n+1-i. Relating that reversal to continuous reflected grid
coordinates still requires the appropriate cell/endpoint convention;
this module does not assert an identity for rounded real coordinates.
That is a remaining application step, not a defect in the finite theorem.

## Scope and trust

The exact used inverse source has SHA256
`cd5af3cf32a12d55ff2c7499b5d47e05b1d5192d3675b837ca053a647cf6d39e`;
its independent assembly review is `reviews/toeplitz-inverse-review.md`.
This review also expressly excludes independent review of this
reviewer's own weighted-factorization, weighted-binomial, and Fourier
proof internals. Their statements are reused through the actual inverse
theorem; the new rewriting and reversal arguments are independently
reviewed here.

A read-only scan of the 12-module project import closure found no
`sorry`, `admit`, custom axiom, unsafe declaration, `native_decide`, or
`Challenge` import. There is no new computation certificate or finite
sampling check. All conclusions agree with the prior statement lock.

The frozen manuscript's equations (26)–(29), in
`original-proof/solution.md` SHA256
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`,
still require a uniform kernel limit and its trace consequences. These
finite identities supply ingredients toward that input; they prove no
uniform convergence, diagonal convergence, or limiting trace by
themselves. MF-21 remains incomplete, and no original-target count or
GitHub Comparator success is claimed.
