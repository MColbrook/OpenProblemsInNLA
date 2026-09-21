# Independent bulk-decay and statement-bridge review

Date: 20 September 2026.
Reviewer: /root/mf21_restart_manuscript.
Verdict: **APPROVE**, limited to the three intermediate results below.
No material mathematical or source-fidelity issue was found.

This is a separate review from fixed-index-numerics-review.md. It applies
the source-fidelity, proof-correctness, reuse, and trust-gap questions in
/Users/georgestepaniants/Research/project/lean-verification/REFEREE_STANDARDS.md,
SHA-256 e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1.
I ran no Lean compiler, LeanCert, or Comparator process and edited no
mathematical manuscript or Lean proof source.

## Exact scope and sources

Reviewed public results:

* MF21Restart.exists_log_sq_bulk_scale_gain.
* MF21Restart.complex_fourier_eq_cosine.
* MF21Restart.bulk_cutoff_pos.

The StatementBridges helpers symbol_neg, integral_symbol_sin, and
fourier_integrand were also reviewed in full.

| Source, relative to the project root | SHA-256 |
| --- | --- |
| MF21Restart/BulkDecay.lean | 2d768009100ca3c3659739bc4c7de26999e1a866fb8b3c2b1d876ae50bdc7582 |
| MF21Restart/StatementBridges.lean | 90992b2cf34bbbefdf9da9c04b814a693faba7ec8d48b16bdf8d00948c4db057 |
| BULK_STATEMENT.md | d0e35b3f18c489db6f38c1902c1355f110003cfaede72e51940c8fcc70849ab2 |
| MF21Restart/Definitions.lean | 35a74047a81a9b7526e9bf039880ca8f07ae33314e2b5b960ab254e02fca4b51 |
| STATEMENTS.md | 6709fd19a3765c83ce16986780963e1f22ae49472b5ea7f013e968f37ab27691 |
| Audit.lean | 99040f11643ac13985d3319dddd8b689d35a02593a7cbb528b216b2e0a1b7eba |

I independently read and hashed these sources. The two reviewed theorem
modules were unchanged between the initial mathematical review and the
coordinator's frozen-source notification.

The unchanged manuscript is at commit
eb37bc17a462177f57efa270e9a9f9b17e9d88e2, SHA-256
6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa.
The bulk ingredient corresponds to the step following (25), manuscript
lines 298–308. The bridges address the original Fourier coefficient and
the cutoff conventions recorded in STATEMENTS.md.

## Bulk statement fidelity

BulkDecay.lean, lines 24–29, quantifies in the correct order:
for each c>0 and natural q there exists one N such that the inequality
holds for every n>=N and every admissible natural j.
N is chosen before j, so this is a uniform bound rather than a
fixed-index limit.

The hypothesis is exactly

    ceil(log(n+2)^2) <= j.

There is no replacement by a larger multiple of log(n+2)^2, no extra
polynomial or logarithmic factor in the cutoff, and no restriction
on j beyond that original lower bound. The theorem does not require
j<=n; this makes its conclusion stronger than the estimate needed for
the finite spectrum, not weaker.

The conclusion

    (n+2) j^q exp(-c j) <= 1

gives the required extra factor h=1/(n+2). For the manuscript,
q=2m-1, so a previously established error bound
A h^(2m) j^(2m-1) exp(-c j) becomes A h^(2m+1) in this bulk region.
The Taylor remainder remains a separate estimate; no exponential factor
is incorrectly assigned to it.

The theorem assumes no spectral estimate, asymptotic conclusion, or
unproved auxiliary limit. The assumption c>0 is necessary: at c=0
and q=0 the displayed inequality cannot hold for large n. Allowing all
natural q, including q=0, is natural and causes no endpoint problem.

## Bulk proof correctness

Lines 30–40 reuse the pinned Mathlib theorem
tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero with rate c/2, obtaining a
uniform real threshold A above which
x^q exp(-(c/2)x)<1.
The conversion from the real exponent q to a natural power is exact.

Lines 42–49 prove log(n+2)->infinity and choose N such that, for n>=N,

    L=log(n+2) >= max(A, 1, 2/c).

These are requirements on the eventual n cutoff constructed in the
proof; they are not additional hypotheses imposed on the bulk index.

Lines 53–70 use L>=1 and the natural-ceiling inequality to obtain

    j >= L^2 >= L >= A.

Thus the first half of the exponential uniformly absorbs j^q.
This argument remains valid if the threshold A from the limit theorem
is negative; it does not silently require A>=0.

Lines 72–88 use L>=2/c, c>0, and j>=L^2 to get
(c/2)j>=L. Hence

    (n+2) exp(-(c/2)j)
      = exp(L-(c/2)j) <= 1.

The identity exp(log(n+2))=n+2 has its required positive argument.
The final product combines these two bounds with
exp(-cj)=exp(-(c/2)j)^2. The factor used in multiplication is
nonnegative, so the inequality direction is preserved.

No monotonicity of j^q exp(-cj) is assumed without proof; the argument
avoids needing that additional lemma. There is no numerical certificate,
finite enumeration, subdivision, or new asymptotic infrastructure.
The documented Mathlib limit supplies the exact needed fact.

## Fourier bridge fidelity and correctness

StatementBridges.lean, lines 44–48, identifies the literal complex
Fourier coefficient with the real coefficient used in Definitions.lean.
It preserves all of the source conventions:

* The interval is [-pi,pi].
* The normalization is 1/(2pi).
* The exponent has the negative sign, exp(-i k theta).
* The frequency k is an arbitrary signed integer.
* The symbol is the original real function (2 sin(theta/2))^(2m).

There is no positive-frequency restriction, missing factor of two, or
change from a complex coefficient to its real part without justification.

The helper symbol_neg, lines 15–16, proves evenness using the even exponent
2m. It is valid also at m=0. The helper integral_symbol_sin, lines 18–28,
then substitutes theta->-theta in the symmetric interval and obtains
minus the integral equal to the integral. This is the correct orientation
and establishes the vanishing imaginary contribution.

The integrand identity, lines 30–40, is the exact Euler expansion
exp(-ik theta)=cos(k theta)-i sin(k theta), with explicit compatible
real, integer, and complex casts. The sign of the sine term is correct.

The main proof separately establishes interval integrability of both
continuous components before subtracting their integrals. Pulling out the
constant i, commuting the real embedding with integration, and applying
the odd-integral identity give the stated real coefficient with its
normalization unchanged. Integrability is not assumed or hidden in a
definition.

This is a concrete coefficient-identification theorem. It does not
assert any eigenvalue asymptotics or construct the determinant argument.

## Positive cutoff and absence of strengthened bulk hypotheses

StatementBridges.lean, lines 67–76, proves

    1 <= ceil(log(n+2)^2)

for every natural n. Since n+2>1, its logarithm and its square are
strictly positive; a zero natural ceiling would contradict the ceiling
upper bound. The edge case n=0 is included and valid.

Consequently the 1<=j hypothesis written explicitly in BulkBound follows
from its existing cutoff hypothesis by transitivity. It excludes no
index allowed by the original cutoff. The formal bulk predicate has not
been strengthened.

## Proof quality and remaining scope

The proofs use standard continuous-integral, exponential, order, and
limit lemmas. They contain no sorry, admit, custom proof axiom,
unsafe shortcut, or assumed restatement of the desired conclusion.
The helpers are located in proof modules rather than leaked into the
trusted definitions.

These declarations close the stated scalar-decay and coefficient/cutoff
ingredients only. They do not establish the root construction,
determinant error bound (25), index matching, coefficient construction,
or trace obstruction. Combining the scalar decay bound with (25) still
requires the independently proved spectral estimate. This limitation
is stated accurately in the module and statement documentation.

## Actual local evidence

I read the coordinator's immutable run record:

    evidence/runs/20260920T122932972971Z/record.json

SHA-256:
f353da4f082bf1f3020729433d9d33b168ddd715305a257295d6c5c486d12833.
The record reports a serial local run from 12:29:32 to 12:30:35 UTC,
with one thread, 4096 MiB, matching theorem-source hashes, and successful
exit code 0 for the relevant commands:

    env LEAN_NUM_THREADS=1 lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/StatementBridges.olean MF21Restart/StatementBridges.lean
    env LEAN_NUM_THREADS=1 lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/BulkDecay.olean MF21Restart/BulkDecay.lean
    env LEAN_NUM_THREADS=1 lake env lean -j1 -M4096 -o .lake/build/lib/lean/Audit.olean Audit.lean

These executions were performed by the coordinator, not this reviewer.
I independently read the logs and checked their hashes and the current
output hashes:

| Evidence | SHA-256 |
| --- | --- |
| evidence/runs/20260920T122932972971Z/StatementBridges.log | c4bee587ce45589759e5d94b454505dbfdd21ed2148199675b58a2fd8552909d |
| evidence/runs/20260920T122932972971Z/BulkDecay.log | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| evidence/runs/20260920T122932972971Z/Audit.log | ceda464af9cc3d3ed7c01aac8aa7bdb597b717b2d6ee41f2dcc6861e1acbeee9 |
| .lake/build/lib/lean/MF21Restart/StatementBridges.olean | 37ebc4e31adf3ecb65a4320f10960684be57d5368d4becb847102e42b95919df |
| .lake/build/lib/lean/MF21Restart/BulkDecay.olean | 18cbe2e258a26401d580838a2a09caf0e25536a8eb7ddec5c9d01d09da5440df |

The empty BulkDecay compile log is not itself an axiom audit.
The separate Audit.log explicitly includes
MF21Restart.exists_log_sq_bulk_scale_gain, as well as both bridge theorems.
All three list only [propext, Classical.choice, Quot.sound].
The audit's final line reports MF21Restart.Target as a proposition,
not a theorem proving it.

The toolchain and dependency versions in that record are Lean v4.33.1,
LeanCert 621a43d7cf21f87872392a01e874f2f1dbddc926, and Mathlib
0df444a360eaa60ab8c11dca51a86af692955474. I independently checked that
the LeanCert and Mathlib worktrees matched those revisions and were clean.

Packaging caveat: the coordinator reported adding separate Challenge and
Solution library declarations during this run. The record's lakefile hash
is e1294189966f709ebaa9fbf2a6e40285c668f3f2d92378cb99177e3eb6de1cdc;
the subsequently inspected lakefile hash is
30748592b16c7ec9a843d99284cb65e806937a75b35a6d4299def7004cae88fd.
No reviewed theorem source changed. This source-level approval does not
certify the final packaging configuration against the earlier run record;
the coordinator has retained a final frozen-configuration run as a
separate remaining check.

No Comparator or GitHub run is asserted. GitHub run IDs: none.

## Acceptance boundary

Approve the three intermediate results at the recorded source hashes.
There are no material mathematical change requests.

The full canonical target remains unproved, and final packaging and
Comparator acceptance are outside this review. These ingredients do not
increase the count of complete distinct Lean verifications or new
mathematical resolutions.

## Follow-up local evidence resolving the configuration mismatch

After the initial report, I read and hashed the coordinator's final
source-and-pin-stable serial run record:

    evidence/runs/20260920T123258467923Z/record.json

SHA-256:
15ef281248a099015d91151d3c795c54bd1cd7abad080e6b9778bd577ae15006.
It records successful local exits for all nine modules, including
Solution.lean and Challenge.lean, with the unchanged reviewed source hashes.
Its lakefile hash is the final
30748592b16c7ec9a843d99284cb65e806937a75b35a6d4299def7004cae88fd,
so the earlier source-versus-configuration evidence mismatch is resolved.

The accompanying Audit.log has SHA-256
ceda464af9cc3d3ed7c01aac8aa7bdb597b717b2d6ee41f2dcc6861e1acbeee9
and reports the same standard three axioms for all eight intermediate
results. This is additional coordinator-run local Lean evidence inspected
by this reviewer, not an independent compiler execution or a Comparator
result. The scoped APPROVE verdict is unchanged. Comparator remains
unrun and MF21Restart.Target remains unproved.
