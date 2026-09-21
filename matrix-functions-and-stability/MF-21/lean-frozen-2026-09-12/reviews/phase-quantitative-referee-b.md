# Independent review: quantitative actual phase preimages

Verdict: **APPROVE** for
`eigenvalue_eventual_quantitative_phase_preimage`.
Reviewer: `/root/mf21_restart_manuscript`, independently of source author
`/root/mf21_restart_lean_audit`. Completed 20 September 2026 under the
pinned referee rubric, SHA256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

I read the complete source, prior statement lock, retained local test
record/log, and unchanged manuscript Lemma 4, especially (19)--(20).
This review covers the new quantitative argument and its calls to
actual established project theorems. It does not re-review my own
upstream phase-window, coverage, spectral-order, or simple-root proofs;
their independent reviews are separate. The concrete indexing bridge
has my separate independent report.

## Exact evidence

| Artifact | SHA256 |
| --- | --- |
| `MF21Restart/PhaseQuantitative.lean` | `bc649144eeafa74c1f0435e4bb90df7a679780c22cb709f2525b9c32be4b9649` |
| `PHASE_QUANTITATIVE_STATEMENTS.md` | `e2648c5d2579b8e4fc1709164da178bf99e1db0e8a23425a774072fc2e713891` |
| `evidence/logs/phase-quantitative-01.json` | `1dc5855d5d9605e06157181cf7a71735191d29b41f78cdc8eb13b819ec609009` |
| `evidence/logs/phase-quantitative-01.log` | `9ea6530dbd00f67b9d24a8adaf2bd8776e43d93f608565a948a85cbcd418c4bc` |
| `.lake/build/lib/lean/MF21Restart/PhaseQuantitative.olean` | `ede0ea37d1abeacf2a07d66eef94c1a34daf450485c12da15bb56cb23a0db5ad` |

I recomputed these hashes and matched source/log/output to the JSON.
The record reports actual exit code 0 and unchanged source for
`lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/PhaseQuantitative.olean MF21Restart/PhaseQuantitative.lean`,
with `LEAN_NUM_THREADS=1`. The theorem's printed axioms are only
`propext`, `Classical.choice`, and `Quot.sound`. The log also contains
a harmless unused/unreachable `ring` warning. I ran no Lean compiler;
these are observed retained coordinator results. Comparator has not
been run for this claim.

## Statement and mathematical audit

The theorem exactly matches the locked interface. N,J,C,c depend only
on m and work for all n>=N and every original one-based index J<=j<=n,
including j=n. Both theta and y are strictly interior, theta has the
actual original eigenvalue, and y satisfies the exact phase equation.
The displacement is `C*exp(-c*j)/(n+2)`, and both angles are bounded
above by `C*j/(n+2)`. No phase label, spectrum, or estimate is assumed
in its public hypotheses beyond m>=2.

The private IVT proof constructs the exact phase preimage using the
actual endpoints `F(0)=-(m-1)*pi/2` and `F(pi)=(n+1)*pi`. Positive
j and j<=n make both comparisons strict and exclude both endpoints.
The derivative comparison lemma correctly handles both possible
orderings of its arguments, deriving the absolute inverse-distance
bound from the lower derivative `(n+2)/2` on the actual interval.

At the indexed residual zero, Jordan's sine inequality on the actual
quarter-period cell and integer sine periodicity yield
`2*|F(theta)-j*pi| <= pi*|E(theta)|`. If `|eta|<=B`, then the lower
cell edge and theta<=pi give
`n*theta >= j*pi-(B+9*pi/4)`. The constant 9*pi/4 correctly includes
both the pi/4 cell deviation and the subtraction of 2*theta; no
factor is lost. Thus the actual exponential error bound gives
`|E(theta)| <= D*exp(-(c0*pi)*j)` with
`D=C0*exp(c0*(B+9*pi/4))`. Combining the two displayed factor-2
bounds yields exactly the claimed denominator n+2 and numerator pi*D.

The size bounds follow separately from the upper cell edge or exact
phase equation, bounded eta, and j>=1. Enlarging C by the maximum of
the displacement and size constants retains positivity and uniformity.
All interval, index, sign, and derivative hypotheses of imported
lemmas are explicitly discharged. No strengthening of the bulk index
condition or unnoticed n-dependent constant occurs.

The source uses ordinary analytic inequalities and library mean-value
and IVT tools, with no new numerical certificate, proof placeholder,
custom axiom, or hidden literature premise. No material issue found.

## Precise remaining scope

The source deliberately characterizes y by `F_n(y)=j*pi`. It does not
yet identify y with the independently constructed
`Y(j*pi/(n+2),1/(n+2))`; that bridge must still use the actual implicit
equation and its proved interval uniqueness. Therefore this report
approves the quantitative phase-preimage component of (19), not a
completed Y-based (19), full Lemma 4, uniform spectral expansion,
kernel limit, trace obstruction, or original MF-21 Target.
